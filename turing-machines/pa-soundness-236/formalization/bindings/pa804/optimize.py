#!/usr/bin/env python3
"""Complete candidates for PA full soundness, without changing the observer.

Read README.md before interpreting the ledger. Baseline artifacts are immutable.
No claimed source-to-table theorem is inferred from finite testing alone.
"""
from __future__ import annotations
import argparse, ast, hashlib, json, sys
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parent
CODE=ROOT/'baseline/code'
sys.path[:0]=[str(CODE/'compact'),str(CODE)]
import direct
import build
from TMBuilder import subroutine
from backend import totalize_silently
import tm
SOURCE=(CODE/'compact/source.py').read_text()

class Streaming(direct.Direct):
    """Same rank/proof/tuple order and same Boolean records as the baseline.

    Four registers disappear: rank, proof, tuple, back. Optionally bit aliases
    count, whose prefix loop has finished before matrix evaluation starts.
    The theorem command interpreter and exact axiom templates are inherited.
    """
    alias_bit=True
    shared_lookup=True
    canonical=False
    def __init__(self,source):
        build.OmegaBuilder.__init__(self,'def main():\n    while True:\n        emit0()\n',share=False)
        self.reference_source=source
        names=['stage','rest','count','top','stack','program','tag','data',
               'a','b','c','u','selector','env','s1','s2']
        if not self.alias_bit:names.insert(3,'bit')
        for name in names:setattr(self,name,self.reg('k.'+name))
        if self.alias_bit:self.bit=self.count
        function=next(n for n in ast.parse(source).body if isinstance(n,ast.FunctionDef) and n.name=='axiom')
        self.axiom_expressions=[n.body[0].value for n in function.body
            if isinstance(n,ast.If) and isinstance(n.test,ast.Compare)
            and isinstance(n.test.left,ast.Name) and n.test.left.id=='selector']
        self.axiom_expressions.append(function.body[-1].value)
        assert len(self.axiom_expressions)==9
    @subroutine
    def theorem(self):
        # program already contains the decoded proof, whose address was emitted.
        return [self.while_decnz(self.program,[
            self.unpair(self.data,self.s1,self.program),self.move(self.program,self.s1),
            self.divbase(self.u,self.tag,self.data,4),self.move(self.data,self.u),
            self.choose(self.tag,[self.command_axiom(),self.command_generalize(),
                                  self.command_mp(),self.command_drop()])]),self.clear(self.stack)]
    @subroutine
    def bind_coordinate(self):
        return [self.pair(self.c,self.a,self.b),self.push(self.c,self.env,0)]
    @subroutine
    def stream_coordinate(self):
        # Emit coordinate before parsing. A failed prefix becomes truth code 0;
        # that cannot pass any further existential/universal prefix check.
        # All remaining coordinates MUST still be decoded and emitted.
        return [self.unpair(self.b,self.s1,self.rest),self.move(self.rest,self.s1),
            self.copy(self.a,self.b),self.emit_natural(self.a),
            self.label('coordinate',[
                self.label('record',[
                    self.choose(self.selector,[[self.strip_negation(),self.strip_universal(),
                        self.strip_negation(),self.selector.inc],self.strip_universal()]),
                    self.bind_coordinate(),'break_coordinate']),
                self.clear(self.top)]),
            [self.clear(r) for r in (self.a,self.b,self.c,self.u,self.tag,self.data,self.s1,self.s2)]]
    @subroutine
    def lookup_both(self):
        if not self.shared_lookup:
            return [self.unpair(self.a,self.b,self.data),self.lookup(self.a),self.lookup(self.b)]
        # count is zero throughout matrix evaluation except for this local save.
        return [self.unpair(self.a,self.b,self.data),self.lookup(self.a),
                self.move(self.count,self.a),self.move(self.a,self.b),self.lookup(self.a),
                self.move(self.b,self.a),self.move(self.a,self.count)]
    @subroutine
    def matrix_atom(self,kind):
        common=self.lookup_both()
        if kind==1:
            return [common,self.while_decnz(self.b,[self.divbase(self.s1,self.s2,self.a,2),
                self.move(self.a,self.s1),self.clear(self.s2)]),
                self.divbase(self.s1,self.s2,self.a,2),self.clear(self.s1),
                self.move(self.a,self.s2),self.push(self.a,self.program,0)]
        return [common,self.equal(self.u,self.a,self.b),self.push(self.u,self.program,0)]
    @subroutine
    def main(self):
        work=(self.rest,self.top,self.stack,self.program,self.tag,self.data,self.a,
              self.b,self.c,self.u,self.selector,self.env,self.s1,self.s2)
        return [self.copy(self.rest,self.stage),self.unpair(self.count,self.s1,self.rest),
            self.move(self.rest,self.s1),self.count.inc,
            self.copy(self.a,self.count),self.emit_natural(self.a),
            self.unpair(self.program,self.s1,self.rest),self.move(self.rest,self.s1),
            self.copy(self.a,self.program),self.emit_natural(self.a),self.theorem(),
            self.while_decnz(self.count,self.stream_coordinate()),
            self.clear(self.rest),self.clear(self.selector),
            self.label('record',self.matrix()),
            [self.clear(r) for r in work],self.emit_natural(self.bit),self.stage.inc]

class StreamingUnaliased(Streaming):
    alias_bit=False
    shared_lookup=False

class OneStack(Streaming):
    """One stack of tasks/continuations, and one Boolean result register.

    Task 4*f enters formula f. Task 4*b+1 schedules b after saving the left
    truth value. Tasks 2 and 3 combine false/true left with the right result.
    BOTH sides are visited, so hidden universals cannot be skipped.
    """
    @subroutine
    def matrix_atom(self,kind):
        common=[self.lookup_both(),self.clear(self.program)]
        if kind==1:
            return [common,self.while_decnz(self.b,[self.divbase(self.s1,self.s2,self.a,2),
                self.move(self.a,self.s1),self.clear(self.s2)]),
                self.divbase(self.s1,self.s2,self.a,2),self.clear(self.s1),
                self.move(self.program,self.s2)]
        return [common,self.equal(self.program,self.a,self.b)]
    @subroutine
    def matrix_implication(self):
        return [self.unpair(self.a,self.b,self.data),self.scale(self.u,self.b,4),self.u.inc,
                self.push(self.u,self.stack,1),self.scale(self.u,self.a,4),self.push(self.u,self.stack,1)]
    @subroutine
    def matrix_enter(self):
        return [self.if_zero(self.top,[self.clear(self.program),self.program.inc]),
            self.if_nz(self.top,[self.divbase(self.data,self.selector,self.top,4),
                self.choose(self.selector,[self.matrix_implication(),self.matrix_atom(1),
                                          'break_record',self.matrix_atom(3)])])]
    @subroutine
    def after_left(self):
        return [self.program.inc,self.program.inc,self.push(self.program,self.stack,1),
                self.scale(self.a,self.top,4),self.push(self.a,self.stack,1)]
    @subroutine
    def matrix(self):
        return [self.scale(self.a,self.top,4),self.push(self.a,self.stack,1),
            self.while_decnz(self.stack,[self.unpair(self.a,self.s1,self.stack),
                self.move(self.stack,self.s1),self.divbase(self.top,self.tag,self.a,4),
                self.choose(self.tag,[self.matrix_enter(),self.after_left(),
                    [self.clear(self.top),self.clear(self.program),self.program.inc],self.clear(self.top)])]),
            self.if_zero(self.program,self.bit.inc),self.clear(self.program)]

class Canonical(OneStack):
    """Different certificate admission: prefix binders must be n-1,...,0.

    Needs a separate alpha-normalization/proof-coverage bridge. It does NOT
    preserve the old Boolean record function on every proof index.
    """
    canonical=True
    @subroutine
    def bind_coordinate(self):
        return [self.copy(self.c,self.count),self.equal(self.u,self.a,self.c),
                self.if_not_decnz(self.u,'break_record'),self.push(self.b,self.env,0)]
    @subroutine
    def lookup(self,query):
        return [self.copy(self.c,self.env),
            self.while_decnz(query,[self.unpair(self.u,self.s1,self.c),
                                  self.move(self.c,self.s1),self.clear(self.u)]),
            self.unpair(query,self.s1,self.c),self.clear(self.s1)]

class SharedUnpair(OneStack):
    """One common inverse-pairing kernel, with fully counted argument transfers."""
    def __init__(self,source):
        super().__init__(source)
        self.arg0=self.reg('shared.arg0');self.arg1=self.reg('shared.arg1');self.arg2=self.reg('shared.arg2')
    @subroutine
    def unpair(self,a,b,z):
        return [self.move(self.arg2,z),
                direct.Direct.unpair(self,self.arg0,self.arg1,self.arg2),
                self.move(a,self.arg0),self.move(b,self.arg1)]

class SharedPair(OneStack):
    """One common pairing kernel; no uncounted interpreter or arguments."""
    def __init__(self,source):
        super().__init__(source)
        self.arg0=self.reg('shared.arg0');self.arg1=self.reg('shared.arg1');self.arg2=self.reg('shared.arg2')
    @subroutine
    def pair(self,out,a,b):
        return [self.move(self.arg0,a),self.move(self.arg1,b),
                direct.Direct.pair(self,self.arg2,self.arg0,self.arg1),self.move(out,self.arg2)]

class SharedBoth(SharedUnpair):
    @subroutine
    def pair(self,out,a,b):
        return [self.move(self.arg0,a),self.move(self.arg1,b),
                direct.Direct.pair(self,self.arg2,self.arg0,self.arg1),self.move(out,self.arg2)]

VARIANTS={'baseline':direct.Direct,'streaming':StreamingUnaliased,'shared':Streaming,
          'one-stack':OneStack,'canonical':Canonical,'shared-unpair':SharedUnpair,
          'shared-pair':SharedPair,'shared-both':SharedBoth}

def boot_named(named,first_register):
    kept={q for q,_ in named if not q.startswith('init.')}
    answer={key:row for key,row in named.items() if key[0] in kept}
    assert all(row[2] in kept for row in answer.values())
    A='init.0';B='init.boot.B';C='init.boot.C';D='init.boot.D';E='init.boot.E'
    for q,r,w,d,t in [(A,0,1,'R',B),(A,1,1,'L',C),(B,0,0,'L',A),(B,1,0,'L',D),
        (C,0,1,'L',A),(C,1,1,'R','3.'+first_register+'.inc'),
        (D,0,1,'L',B),(D,1,1,'R',E),(E,0,0,'R',D),(E,1,0,'R',B)]:answer[q,r]=(w,d,t,'-')
    return answer

def compile_candidate(cls,out):
    builder=cls(SOURCE);builder.build_tree();builder.generate();labels={}
    for bit in '01':
        builder.tm.states['emit.'+bit,'0']=tm.Transition('1','R','1b.reg.prep_1')
        builder.tm.states['emit.'+bit,'1']=tm.Transition('0','L','6.break.0');labels['emit.'+bit,'1']=bit
    initial=build.counted_initializer(builder);builder.tm.symbols={'0','1'};builder.tm.gc()
    missing=totalize_silently(builder);builder.tm.gc()
    named={(q,int(r)):(int(t.write),t.direction,t.nextstate,labels.get((q,r),'-')) for (q,r),t in builder.tm.states.items()}
    root,measures=build.dag_measures(builder)
    common=dict(initializer=initial,register_order=list(builder.registers),grammar_root=root,
        grammar={str(i):list(builder.sequences[i].seq) for i in sorted(builder.reachable())},
        grammar_names={str(i):builder.sequences[i].name for i in sorted(builder.reachable())},
        grammar_depth=measures[root][0],grammar_zero_depth=measures[root][1],
        totalized_rows=[[q,int(s)] for q,s in sorted(missing)],direct_events=True,
        source_sha256=hashlib.sha256(SOURCE.encode()).hexdigest(),
        generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        variant=cls.__name__,canonical_admission=bool(getattr(cls,'canonical',False)))
    summaries={}; result_rows={}
    assert initial['registers']<=1909 and initial['max_leaf_path']<3822
    for mode,table in [('counted',named),('boot',boot_named(named,common['register_order'][0]))]:
        rows,ids=build.number_rows(table)
        cats=Counter(('bootstrap' if mode=='boot' else 'initializer') if q.startswith('init.') else
             'grammar' if q in common['grammar_names'].values() else
             'register-selection' if q.startswith(('2b.reg.','3.')) else
             'events' if q.startswith(('event.','emit.')) else 'engine-and-totalization' for q in ids)
        meta=dict(common,named_state_to_id=ids,state_ledger=dict(cats))
        if mode=='boot':meta['entry_geometry']=dict(head=-3818,ones=[-3821,-3820]+list(range(3,3822,2)))
        raw=build.write_machine(out/mode/'raw',rows,meta)
        reduced,cert=build.exact_quotient(rows);cert['source_table_sha256']=raw['table_sha256']
        best=build.write_machine(out/mode/'quotient',reduced,dict(parent='raw',quotient=cert,variant=cls.__name__,
              source_sha256=common['source_sha256'],generator_sha256=common['generator_sha256']))
        summaries[mode]=dict(raw=raw['states'],selected=best['states'],rows=best['transitions'],
                ledger=dict(cats),sha256=best['table_sha256'],registers=len(builder.registers))
        result_rows[mode]=(rows,reduced,cert)
    (out/'ledger.json').write_text(json.dumps(summaries,sort_keys=True,indent=2)+'\n')
    return builder,summaries,result_rows

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--variant',choices=['all']+list(VARIANTS),default='all');a=p.parse_args()
    if a.out.exists():raise SystemExit('Output directory must be fresh.')
    ledgers={}
    for name,cls in VARIANTS.items():
        if a.variant!='all' and name!=a.variant:continue
        _,ledger,_=compile_candidate(cls,a.out/name);ledgers[name]=ledger
        if name=='baseline':
            assert ledger['counted']['sha256']=='b69dce81d6397a3de2ab33ddd49f90ae60795542bee5d14c08085b8e50ba4816',ledger
            assert ledger['boot']['sha256']=='2358b4847410f8ec69d0b51d7e7fe93fb5aa1c47877a650de8bd2d9b82356969',ledger
        print(name,json.dumps(ledger),flush=True)
    (a.out/'comparison.json').write_text(json.dumps(ledgers,sort_keys=True,indent=2)+'\n')
if __name__=='__main__':main()
