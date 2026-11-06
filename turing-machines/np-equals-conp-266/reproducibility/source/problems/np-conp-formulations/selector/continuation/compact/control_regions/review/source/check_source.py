"""Independent exact source delta and finite call review.

No producer, source oracle, compiler, optimizer or physical engine is imported.
Prepared-clock fixtures are explicitly separate from literal source clocks.
"""
from copy import deepcopy
from pathlib import Path
import argparse
import ast
import hashlib
import json
import random

OLD_SHA='4f1f6f317eb196b8d09a67439893622a759c43ef4e02e30adae4e04b0eb39515'


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def form(value):return ast.dump(value,include_attributes=False)
def statement(text):return ast.parse(text).body[0]


def body(tree):
    main=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main']
    assert len(main)==1
    outer=[n for n in main[0].body if isinstance(n,ast.While)]
    assert len(outer)==1 and form(outer[0].test)==form(ast.Constant(True))
    inner=[n for n in outer[0].body if isinstance(n,ast.While)]
    assert len(inner)==1 and form(inner[0].test)==form(ast.Constant(True))
    return inner[0].body


def exact_delta(original,selected):
    """The universal source relation has precisely this finite syntactic delta."""
    expected=deepcopy(original);statements=body(expected)
    position=[i for i,n in enumerate(statements) if form(n)==form(statement('clock = (n + 1) ** j'))]
    assert len(position)==1
    at=position[0]
    tail=statements[at+1:]
    clock_loads=0;description_loads=0
    for node in [v for n in tail for v in ast.walk(n)]:
        if isinstance(node,ast.Name) and node.id=='clock':
            assert isinstance(node.ctx,ast.Load)
            node.id='n';clock_loads+=1
        if isinstance(node,ast.Assign) and form(node)==form(statement('digit = j')):
            node.value=ast.Name('e',ast.Load());description_loads+=1
    assert (clock_loads,description_loads)==(2,1)
    statements[at:]=[statement('e = n'),statement('n = (e + 1) ** j'),statement('e = j'),*tail]
    assert form(expected)==form(selected),'source differs from the exact reviewed carrier substitution'
    return dict(clock_loads_redirected=clock_loads,description_loads_redirected=description_loads,
                new_assignments=['e = n','n = (e + 1) ** j','e = j'])


def prefix(i):
    pairs=[];shift=0
    while (i>>shift)&1:
        pairs.append((i>>(shift+1))&1);shift+=2
    description=1
    for bit in pairs:description=(description<<1)|bit
    return description,len(pairs)


def record(description,ordinal):
    """v2(d+1) counts low trailing ones, including an all-ones finite word."""
    for _ in range(ordinal+1):
        number=description+1
        length=(number & -number).bit_length()-1
        description>>=length+1
    return length,description


def attempt(description,input_value,certificate,clock):
    positive={k for k in range(input_value.bit_length()) if input_value>>k&1}
    negative={-k-1 for k in range(certificate.bit_length()) if certificate>>k&1}
    tape=positive|negative
    head,facing,state=0,1,1
    for _ in range(clock):
        if state==0:break
        encoded,_=record(description,state+int(head in tape)-1)
        write=encoded&1
        facing*= -1 if encoded&2 else 1
        state=encoded>>2
        if write:tape.add(head)
        else:tape.discard(head)
        head+=facing
    return int(state==0)


def expected_trace(j,i,prepared=None):
    description,n=prefix(i)
    clock=(n+1)**j if prepared is None else prepared
    trace=[];answers=[]
    for phase,d,x,t,bound in [(0,description,0,n,description),(1,j,i,clock,1<<clock)]:
        accepted=0
        for certificate in reversed(range(bound)):
            accepted=attempt(d,x,certificate,t)
            trace.append((phase,d,x,certificate,t,accepted))
            if accepted:break
        answers.append(accepted)
    return answers[0]^answers[1],trace,tuple(answers)


class Isolate(ast.NodeTransformer):
    """Terminate exactly at the original comparison's refutation/continue join."""
    def __init__(self):self.loop_depth=0
    def visit_While(self,node):
        self.loop_depth+=1;node=self.generic_visit(node);self.loop_depth-=1
        return node
    def visit_Break(self,node):
        return node if self.loop_depth else ast.Return(ast.Constant(0))


class Observe(ast.NodeTransformer):
    def __init__(self):self.phases=0
    def visit_Assign(self,node):
        if isinstance(node.value,ast.BinOp) and isinstance(node.value.op,ast.Pow):
            node.value=ast.IfExp(ast.Compare(ast.Name('_prepared',ast.Load()),[ast.Is()],[ast.Constant(None)]),
                node.value,ast.Name('_prepared',ast.Load()))
        return node
    def visit_While(self,node):
        is_attempt=(isinstance(node.test,ast.Name) and node.test.id=='steps' and
            any(isinstance(n,ast.If) and form(n.test)==form(ast.Name('state',ast.Load())) for n in node.body))
        if not is_attempt:return self.generic_visit(node)
        phase=self.phases;self.phases+=1
        descriptions=[n.value.id for n in ast.walk(node) if isinstance(n,ast.Assign) and
            len(n.targets)==1 and form(n.targets[0])==form(ast.Name('digit',ast.Store())) and isinstance(n.value,ast.Name)]
        assert len(descriptions)==1
        before=ast.Assign([ast.Name('_snapshot',ast.Store())],ast.Tuple([
            ast.Constant(phase),*[ast.Name(n,ast.Load()) for n in (descriptions[0],'right','left','steps')]],ast.Load()))
        after=statement('_observe(_snapshot, int(state == 0))')
        return [before,self.generic_visit(node),after]


def comparison_function(tree,trace):
    statements=deepcopy(body(tree))
    assert form(statements[-1])==form(statement('i += 1'))
    isolated=ast.FunctionDef('comparison',ast.arguments(posonlyargs=[],args=[ast.arg('j'),ast.arg('i'),ast.arg('_prepared')],
        vararg=None,kwonlyargs=[],kw_defaults=[],kwarg=None,defaults=[ast.Constant(None)]),
        statements[:-1]+[ast.Return(ast.Constant(1))],[],None,None)
    isolated=Isolate().visit(isolated)
    observer=Observe();isolated=observer.visit(isolated);assert observer.phases==2
    module=ast.fix_missing_locations(ast.Module([isolated],[]))
    namespace={'_observe':lambda before,accepted:trace.append((*before,accepted))}
    exec(compile(module,'<reviewed finite comparison>','exec'),namespace)
    return namespace['comparison']


def source_mutations(original,selected):
    cases=[]
    def reject(label,edit):
        bad=deepcopy(selected);edit(bad)
        try:exact_delta(original,bad)
        except AssertionError:cases.append(label)
        else:raise AssertionError('source mutation accepted: '+label)
    def replace_once(tree,old,new):
        for parent in ast.walk(tree):
            for name,value in ast.iter_fields(parent):
                if isinstance(value,list):
                    for i,item in enumerate(value):
                        if isinstance(item,ast.AST) and form(item)==form(statement(old)):
                            value[i]=statement(new);return
        raise AssertionError('mutation source absent')
    for label,old,new in [
        ('length copied too late','e = n','e = 0'),
        ('wrong normalized base','n = (e + 1) ** j','n = e ** j'),
        ('wrong exponent','n = (e + 1) ** j','n = (e + 1) ** i'),
        ('wrong candidate master','e = j','e = i'),
        ('candidate high input bits lost','right = i','right = 0'),
        ('reference certificate bound shrunk','branch = e','branch = n'),
        ('simulator state reset removed','state = 1','state = 0'),
    ]:reject(label,lambda t,o=old,n=new:replace_once(t,o,n))
    return cases


def run(source,reference):
    assert sha(reference)==OLD_SHA
    old,new=ast.parse(Path(reference).read_text()),ast.parse(Path(source).read_text())
    delta=exact_delta(old,new)
    actual=[(j,i,None) for j in range(3) for i in range(32)]
    actual += [(j,i,None) for j in (3,7,31,127) for i in (0,2,6,14,126,1022)]
    prepared=[(j,i,c) for j in (0,1,2,3,7,15,31,63,495,65535) for i in (0,1,2,3,7,15,31,63) for c in (0,1,2,4)]
    rng=random.Random(266)
    prepared += [(rng.randrange(1<<20),rng.randrange(256),rng.randrange(6)) for _ in range(96)]
    seen=set();attempts=0;identities=[]
    for case in actual+prepared:
        answer,expected,outcomes=expected_trace(*case);seen.add(outcomes)
        traces=[]
        for tree in (old,new):
            trace=[];call=comparison_function(tree,trace)
            assert call(*case)==answer,('comparison result',case)
            assert trace==expected,('attempt domain/order/reset/semantics',case)
            traces.append(trace)
        assert traces[0]==traces[1]
        attempts+=len(expected)
        identities.append((case,answer,len(expected),outcomes))
    assert seen=={(0,0),(0,1),(1,0),(1,1)}
    for n in range(129):
        assert record((1<<n)-1,0)==(n,0)
        assert record((1<<n)-1,1)==(0,0)
    for i in range(0,2048,2):assert prefix(i)==(1,0)
    return dict(format='np-conp-control-independent-source-v1',reviewer='internal-model-reviewer',
        source_sha256=sha(source),reference_sha256=sha(reference),checker_sha256=sha(__file__),exact_delta=delta,
        actual_clock_cases=len(actual),prepared_clock_cases=len(prepared),attempts_per_source=attempts,
        exact_attempt_traces_compared=True,comparison_outcomes=sorted(map(list,seen)),
        all_ones_virtual_terminators=258,even_input_prefix_cases=1024,
        fixtures_sha256=hashlib.sha256(json.dumps(identities,sort_keys=True).encode()).hexdigest(),
        mutations_rejected=source_mutations(old,new),
        scope='exact AST carrier substitution and finite source-call evidence; conventional universal argument recorded separately; no physical or blank execution claim')


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('source','reference','out'):p.add_argument('--'+name,type=Path,required=True)
    a=p.parse_args();result=run(a.source,a.reference)
    a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))
