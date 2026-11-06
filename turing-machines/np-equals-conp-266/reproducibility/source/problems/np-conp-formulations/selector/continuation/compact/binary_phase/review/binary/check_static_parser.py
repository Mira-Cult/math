"""Nonauthor binary/domain review for the ordinal-reuse continuation.

Reuses the previous independently written tuple graph, abstract transfer and
certificate equations explicitly, without importing the producer compiler.
The source CFG reconstruction is copied from that checker, with its old
accept-AST-identity assertion removed because the new source has a separately
reviewed equivalence proof. Every remaining allocation equation is retained.
"""
from collections import defaultdict
from copy import deepcopy
from pathlib import Path
import argparse
import ast
import hashlib
import importlib.util
import json
import subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
COMPACT=ROOT.parent
SOURCE=ROOT/'control/parser/source.py'
SOURCE_SHA='46f2a7273f0dfeca71c851f02b5e364836f62fad4eef622ea6a8ee48e6515de5'
PRIOR=COMPACT/'phase_search/review/certificate_engine/check_selected.py'

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result);return result

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def jd(value):return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def load(folder):return {p.name:json.loads(p.read_text()) for p in Path(folder).glob('*.json')}
prior=module('binary_phase_prior_independent_static',PRIOR)
prior.SOURCE=SOURCE;prior.SOURCE_SHA=SOURCE_SHA
endpoint=prior.endpoint
SEMANTIC_EXCLUSIONS=prior.SEMANTIC_EXCLUSIONS
storage=prior.storage

def source_cfg(source, allocation):
    """Reconstruct source CFG edges/read sets independently from the AST."""
    tree = ast.parse(source.read_text())
    functions = {n.name: n for n in tree.body if isinstance(n, ast.FunctionDef)}
    assert set(functions) == set(allocation['functions'])
    totals = {}
    for name, function in functions.items():
        record = allocation['functions'][name]
        variables = set(record['colours'])
        returns = record['returns']
        assert record['parameters'] == [arg.arg for arg in function.args.args]

        def reads(expr):
            return {n.id for n in ast.walk(expr) if isinstance(n, ast.Name)
                    and isinstance(n.ctx, ast.Load) and n.id in variables}

        def writes(expr):
            return {n.id for n in ast.walk(expr) if isinstance(n, ast.Name)}

        exit_key = ('exit', 0)
        expected = {exit_key: (set(), set(returns), [])}

        def block(statements, following, break_to=None):
            for stmt in reversed(statements):
                if isinstance(stmt, ast.While):
                    key = ('while', stmt.lineno)
                    after_else = block(stmt.orelse, following, break_to)
                    body = block(stmt.body, key, following)
                    expected[key] = (set(), reads(stmt.test), [body, after_else])
                elif isinstance(stmt, ast.If):
                    key = ('if', stmt.lineno)
                    yes = block(stmt.body, following, break_to)
                    no = block(stmt.orelse, following, break_to)
                    expected[key] = (set(), reads(stmt.test), [yes, no])
                elif isinstance(stmt, ast.Assign):
                    key = ('assign', stmt.lineno)
                    definitions = set().union(*(writes(t) for t in stmt.targets))
                    expected[key] = (definitions, reads(stmt.value), [following])
                elif isinstance(stmt, ast.AugAssign):
                    key = ('augment', stmt.lineno)
                    definitions = writes(stmt.target)
                    expected[key] = (definitions, reads(stmt.value) | definitions, [following])
                elif isinstance(stmt, ast.Return):
                    key = ('return', stmt.lineno)
                    expected[key] = (set(returns), reads(stmt.value), [exit_key])
                elif isinstance(stmt, ast.Break):
                    assert break_to is not None
                    key = ('break', stmt.lineno)
                    expected[key] = (set(), set(), [break_to])
                else:
                    assert isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)
                    assert isinstance(stmt.value.func, ast.Name) and stmt.value.func.id == 'beep'
                    key = ('beep', stmt.lineno)
                    expected[key] = (set(), set(), [following])
                assert key != exit_key
                following = key
            return following

        entry = block(function.body, exit_key)
        cfg = record['cfg']
        supplied = cfg['nodes']
        keys = [(n['kind'], n['line']) for n in supplied]
        assert len(keys) == len(set(keys)) and set(keys) == set(expected)
        assert keys[cfg['entry']] == entry and keys[cfg['exit']] == exit_key
        for key, node in zip(keys, supplied):
            definitions, uses, targets = expected[key]
            assert set(node['defines']) == definitions and set(node['uses']) == uses
            assert [keys[t] for t in node['successors']] == targets
            outgoing = set().union(*(set(supplied[t]['live_in']) for t in node['successors']))
            assert set(node['live_out']) == outgoing
            assert set(node['live_in']) == uses | (outgoing - definitions)
            # Values needed simultaneously, simultaneous destinations, and
            # every newly defined value versus surviving values are separate.
            required = [set(node['live_in']), outgoing, definitions,
                        definitions | outgoing]
            for names in required:
                assert len({record['colours'][v] for v in names}) == len(names)
        for variable, neighbours in record['graph'].items():
            assert variable in variables
            for neighbour in neighbours:
                assert variable in record['graph'][neighbour]
                assert record['colours'][variable] != record['colours'][neighbour]
        height = allocation['heights'][name]
        for variable, colour in record['colours'].items():
            assert allocation['mapping'][name+'.'+variable] == f'$liveframe.{height}.{colour}'
        for node in ast.walk(function):
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in functions:
                assert allocation['heights'][node.func.id] < height
        totals[name] = dict(nodes=len(keys), variables=len(variables),
                            frame_size=allocation['frame_sizes'][name])
    return totals

def runtime(parent,data):
    previous=COMPACT/'phase_search/machines/normalized'
    repo=next(p for p in HERE.parents if (p/'RESEARCH_PROTOCOL.md').is_file())
    commit='f997ea51504460495a77fbb00c338a468db023b6'
    for name in ('raw.tm','names.json'):
        p=previous/name
        committed=subprocess.check_output(['git','-c','protocol.allow=never','show',commit+':'+p.relative_to(repo).as_posix()],cwd=repo)
        assert p.read_bytes()==committed
    def named(folder,names):
        reverse={q:name for name,q in names.items()}
        assert len(reverse)==len(names)
        return {(reverse[q],bit):(w,d,reverse[t],event) for (q,bit),(w,d,t,event) in endpoint.table(folder/'raw.tm')[1].items()}
    oldnames=load(previous)['names.json'];names=data['names.json']
    old=named(previous,oldnames);current=named(parent,names)
    kernels={name for name in names if not name.startswith(('compact_grammar_','main(', '3.'))}
    assert kernels <= set(oldnames)
    for name in kernels:
        for bit in (0,1):assert current[name,bit]==old[name,bit],name
    order=data['grammar.json']['registers'];native=data['native-runtime.json']['operands']
    assert order[:len(native)]==native
    operations={name for name in names if name.startswith('3.')}
    for op in operations:
        kind,register=endpoint.operand(op)
        if kind=='half':
            assert current[op,0]==(1,'R','2h.native_half.prep',0)
            assert current[op,1]==(0,'R',f'2h.native_half.select.{native.index(register)}',0)
        else:
            assert current[op,0]==(1,'R','1b.reg.prep_1',0)
            assert current[op,1]==(int(kind=='decnz'),'R',f'shared.selector.select.{order.index(register)+1}',0)
    maximum=max(len(path) for path,*_ in endpoint.Graph(data['grammar.json']).leaves)
    assert maximum==data['selector.json']['max_leaf_path']<3822
    assert len(order)==data['selector.json']['registers']<=1909
    for name,digest in data['metadata.json']['producer_inputs'].items():assert sha(SOURCE.parent/name)==digest,name
    assert data['metadata.json']['parent_direct_lowering_sha256']==sha(ROOT/'control/build_skip.py')
    return dict(inherited_producer=commit,exact_common_runtime_rows=2*len(kernels),new_runtime_rows=0,
        checked_entries=len(operations),native_operands=native,maximum_path=maximum,initial_zero_fields=1909)


def domain(parent,selected,pdata,sdata):
    names=pdata['names.json'];raw_header,raw=endpoint.table(parent/'raw.tm')
    assert set(names.values())==set(range(int(raw_header['states']))) and len(names)==len(set(names.values()))
    requested={(name,int(bit)) for name,bit in pdata['selector.json']['new_totalized_rows']}
    assert requested==set(SEMANTIC_EXCLUSIONS.items())
    blocked={(names[name],bit) for name,bit in requested}
    sink=names['silent.sink'];blocked|={(sink,0),(sink,1)}
    assert {(q,z) for (q,z),(_,_,t,_) in raw.items() if t==sink}==blocked
    preimages=defaultdict(list);first=pdata['quotient.json']
    for q in names.values():preimages[endpoint.mapped(first,q)].append(q)
    holes={(q,z) for q,olds in preimages.items() for z in (0,1) if all((old,z) in blocked for old in olds)}
    supplied=sdata['domain.json'];header,old=endpoint.table(parent/'machine.tm')
    assert supplied['source_sha256']==SOURCE_SHA and supplied['control_sha256']==sha(parent/'machine.tm')
    assert supplied['names_sha256']==sha(parent/'names.json')
    assert supplied['raw_quotient_sha256']==sha(parent/'quotient.json')
    assert supplied['source_request_file_sha256']==sha(parent/'selector.json')
    assert {tuple(x) for x in supplied['holes']}==holes
    assert supplied['preimages']=={str(q):preimages[q] for q,_ in sorted(holes)}
    assert supplied['sink']==endpoint.mapped(first,sink)
    assert all(old[key][2]==supplied['sink'] for key in holes)
    newheader,new=endpoint.table(selected/'raw.tm');assert newheader==header
    assert all(old[key]==new[key] for key in old if key not in holes)
    completion=sdata['completion.json']
    assert completion['source_sha256']==sha(parent/'machine.tm') and completion['target_sha256']==sha(selected/'raw.tm')
    assert completion['retained_rows']==len(old)-len(holes)
    assert completion['changes']==[dict(state=q,read=z,before=list(old[q,z]),after=list(new[q,z])) for q,z in sorted(holes)]
    _,_,pc=endpoint.row_maps(parent);mapping,_,sc=endpoint.row_maps(selected)
    assert endpoint.mapped(mapping,0)==0 and [q for q in range(len(old)//2) if endpoint.mapped(mapping,q)==1]==[1]
    for folder,data in ((parent,pdata),(selected,sdata)):
        e=data['event-quotient.json']
        assert e['source_B']==1 and e['time_shift']==-1
        assert e['source_table_sha256']==sha(folder/'machine.tm')
        assert e['predecessor_sha256']==sha(folder/'ingress-prequotient.tm')
        assert e['result_sha256']==sha(folder/'events.tm')
        rows=endpoint.table(folder/'machine.tm')[1]
        assert all(rows[1,z][2]!=1 for z in (0,1))
    return dict(raw_named_exclusions=len(requested),holes=[list(k) for k in sorted(holes)],
        retained_rows=len(old)-len(holes),parent_counts=pc,selected_counts=sc,
        completion_quotient_equations=len(new),event_quotient_equations=2*sc['B_exit'])


def equations(before,after,mapping):
    assert {endpoint.mapped(mapping,q) for q in range(len(before)//2)}==set(range(len(after)//2))
    assert endpoint.mapped(mapping,0)==0
    for (q,z),(w,d,t,e) in before.items():assert after[endpoint.mapped(mapping,q),z]==(w,d,endpoint.mapped(mapping,t),e)


def reject(call):
    try:call()
    except (AssertionError,KeyError,IndexError,ValueError):return
    raise AssertionError('deliberately damaged certificate was accepted')


def adversarial(parent,selected,pdata,sdata):
    checks=[]
    bad=deepcopy(pdata);cert=bad['contextual-tree-certificate.json'];g=endpoint.Graph(cert['input_grammar'])
    value=list(cert['states_at_occurrences'][g.entry]);value[0]='2';cert['states_at_occurrences'][g.entry]=''.join(value)
    reject(lambda:storage(bad));checks.append('false contextual zero entry')
    bad=deepcopy(pdata)
    for pair in bad['pre-projection-grammar.json']['nodes']:
        for child in pair:
            if child.get('op','').startswith('3.$native-half:'):
                child['op']='3.'+child['op'].split(':',1)[1];break
        else:continue
        break
    bad['control-certificate.json']['finite_control_output_grammar_sha256']=jd(bad['pre-projection-grammar.json'])
    bad['bank-projection.json']['before_grammar_sha256']=jd(bad['pre-projection-grammar.json'])
    reject(lambda:storage(bad));checks.append('HALF reinterpreted as decrement with updated digests')
    bad=deepcopy(pdata);name=bad['bank-projection.json']['removed_registers'][0]
    bad['bank-projection.json']['removed_interpretation'][name]=1
    reject(lambda:storage(bad));checks.append('nonzero omitted coordinate')
    bad=deepcopy(pdata);cert=bad['coalescence-invariant.json'];g=endpoint.Graph(cert['input_grammar'])
    value=list(cert['states_at_occurrences'][g.entry]);value[-1]='2';cert['states_at_occurrences'][g.entry]=''.join(value)
    bad['bank-coalescence.json']['invariant_sha256']=jd(cert)
    reject(lambda:storage(bad));checks.append('false sharing entry with updated digest')
    bad=deepcopy(pdata);colours=bad['allocation.json']['functions']['accept']['colours'];colours['state']=colours['right']
    reject(lambda:source_cfg(SOURCE,bad['allocation.json']));checks.append('live source alias')
    bad=deepcopy(sdata);bad['domain.json']['holes'].append([0,0])
    reject(lambda:domain(parent,selected,pdata,bad));checks.append('invented hole')
    bad=deepcopy(sdata);bad['domain.json']['preimages'][str(bad['domain.json']['holes'][0][0])]=[]
    reject(lambda:domain(parent,selected,pdata,bad));checks.append('missing raw preimages')
    bad=deepcopy(pdata);bad['selector.json']['new_totalized_rows'].append(['beep','0'])
    reject(lambda:domain(parent,selected,bad,sdata));checks.append('unjustified exclusion')
    before=endpoint.table(selected/'raw.tm')[1];after=endpoint.table(selected/'machine.tm')[1];mapping=sdata['quotient.json']
    for field,label in ((0,'write'),(1,'move'),(2,'target'),(3,'event color')):
        bad=dict(after);row=list(bad[0,0]);row[field]=[1-row[0],'L' if row[1]=='R' else 'R',(row[2]+1)%(len(after)//2),1-row[3]][field];bad[0,0]=tuple(row)
        reject(lambda:equations(before,bad,mapping));checks.append('damaged '+label)
    bad=deepcopy(mapping);bad['1']=0;reject(lambda:equations(before,after,bad));checks.append('B merged with start')
    ingress=endpoint.table(selected/'ingress-prequotient.tm')[1];marked=endpoint.table(selected/'events.tm')[1]
    bad=dict(marked);key=next(k for k,v in marked.items() if v[3]);bad[key]=(*bad[key][:3],0)
    reject(lambda:equations(ingress,bad,sdata['event-quotient.json']['mapping']));checks.append('event erased')
    bad=deepcopy(sdata);bad['event-quotient.json']['time_shift']=0
    reject(lambda:domain(parent,selected,pdata,bad));checks.append('event shift erased')
    return checks


def run(parent,selected):
    assert sha(SOURCE)==SOURCE_SHA
    pdata,sdata=load(parent),load(selected)
    for folder,data in ((parent,pdata),(selected,sdata)):
        m=data['metadata.json'];assert m['source_sha256']==SOURCE_SHA
        for key,name in (('raw_table_sha256','raw.tm'),('table_sha256','machine.tm'),('event_table_sha256','events.tm')):assert m[key]==sha(folder/name)
    return dict(format='np-conp-binary-phase-independent-static-v1',reviewer='/root (nonauthor of direct-branches source/lowering)',
        source_sha256=SOURCE_SHA,checker_sha256=sha(Path(__file__)),reused_checker_sha256=sha(PRIOR),
        source_allocation=source_cfg(SOURCE,pdata['allocation.json']),storage=storage(pdata),runtime=runtime(parent,pdata),
        fresh_domain=domain(parent,selected,pdata,sdata),damaged_certificates_rejected=adversarial(parent,selected,pdata,sdata),
        artifacts={label:{p.name:sha(p) for p in sorted(folder.iterdir()) if p.is_file()} for label,folder in (('parent',parent),('selected',selected))},
        scope='Independent source allocation, abstract closure, storage and literal row checks. Coordinator authored the new completion wrapper; its review is author verification and separately reviewed by the nonauthor source reviewer. Finite physical execution and mathematical source review are separate.')

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--parent',type=Path,required=True);parser.add_argument('--selected',type=Path,required=True);parser.add_argument('--out',type=Path,required=True)
    a=parser.parse_args();result=run(a.parent,a.selected);a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('artifacts',)},sort_keys=True,indent=2))
