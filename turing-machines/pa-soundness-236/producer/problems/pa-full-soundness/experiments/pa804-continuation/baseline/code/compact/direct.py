"""Hand-allocated PA238-style implementation of source.py.

All data registers begin zero. Only stage persists between completed frames.
Constructor macros use the original dual-Cantor destructive pair/unpair and
RPN formula-stack discipline. The fixed observer receives the same unary
records as source.py. The constructor AST is compiled to finite control;
there is no free tape program. This file is a producer implementation, not an
independent correctness certificate.
"""
from __future__ import annotations
import argparse
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
CODE=HERE.parent
sys.path.insert(0,str(CODE))
import build
from TMBuilder import subroutine
from backend import totalize_silently
import tm


class Direct(build.OmegaBuilder):
    def __init__(self, source):
        super().__init__('def main():\n    while True:\n        emit0()\n',share=False)
        self.reference_source=source
        for name in ('stage','rank','proof','tuple','rest','count','back','bit',
                     'top','stack','program','tag','data','a','b','c','u','selector','env',
                     's1','s2'):
            setattr(self,name,self.reg('k.'+name))
        function=next(n for n in ast.parse(source).body if isinstance(n,ast.FunctionDef) and n.name=='axiom')
        self.axiom_expressions=[n.body[0].value for n in function.body
            if isinstance(n,ast.If) and isinstance(n.test,ast.Compare)
            and isinstance(n.test.left,ast.Name) and n.test.left.id=='selector']
        self.axiom_expressions.append(function.body[-1].value)
        assert len(self.axiom_expressions)==9

    @subroutine
    def pair(self,out,a,b):
        # out=0. Consume a,b, return P(a,b)=triangle(a+b)+b.
        return [self.label('pair',[self.while_decnz(b,[a.inc,out.inc]),
            [a.decnz,[[out.inc,self.while_decnz(a,b.inc)],'continue_pair']]])]

    @subroutine
    def unpair(self,a,b,z):
        # a=b=0. Consume z, return its dual Cantor coordinates.
        return [self.while_decnz(z,[b.inc,self.if_not_decnz(a,self.while_decnz(b,a.inc))])]

    @subroutine
    def divbase(self,q,r,x,base):
        # q=r=0, base is a fixed positive build-time integer; consume x.
        body=[self.clear(r),q.inc]
        for _ in range(base-1):
            body=[r.inc,self.if_decnz(x,body)]
        return [self.while_decnz(x,body)]

    @subroutine
    def scale(self,out,x,factor):
        return [self.while_decnz(x,[out.inc]*factor)]

    @subroutine
    def push(self,value,stack,proper):
        # Both inputs consumed into stack. s1=s2=0 at both boundaries.
        return [self.move(self.s1,value),self.move(self.s2,stack),
                self.pair(stack,self.s1,self.s2),[stack.inc]*proper]

    @subroutine
    def pop(self,value,stack,proper):
        # value=0. Missing implicit stack entries are 0.
        return [[self.dec(stack)]*proper,self.unpair(self.s1,self.s2,stack),
                self.move(value,self.s1),self.move(stack,self.s2)]

    def choose(self,register,bodies):
        if len(bodies)==1:
            return [self.clear(register),bodies[0]]
        label='choose_'+str(len(self.sequences))+'_'+str(len(bodies))
        return [self.label(label,[[register.decnz,[self.choose(register,bodies[1:]),'break_'+label]],bodies[0]])]

    @subroutine
    def formula_parameter(self,register):
        return [self.push(self.top,self.stack,0),self.copy(self.top,register)]

    @subroutine
    def formula_one(self):
        return [self.push(self.top,self.stack,0),self.top.inc]

    @subroutine
    def constructor(self,residue):
        return [self.unpair(self.s1,self.s2,self.stack),self.move(self.stack,self.s2),
                self.pair(self.s2,self.s1,self.top),self.scale(self.top,self.s2,4),
                [self.top.inc]*residue]

    @subroutine
    def negation(self):
        return [self.formula_one(),self.constructor(0)]

    @subroutine
    def existential(self):
        return [self.negation(),self.constructor(2),self.negation()]

    @subroutine
    def conjunction(self):
        return [self.negation(),self.constructor(0),self.negation()]

    def expression(self,node):
        if isinstance(node,ast.Name):
            assert node.id in ('a','b','c','u')
            return self.formula_parameter(getattr(self,node.id))
        assert isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and not node.keywords
        name=node.func.id
        if name in ('imp','member','all_','equal'):
            assert len(node.args)==2
            operation=self.constructor(('imp','member','all_','equal').index(name))
        else:
            assert name in ('neg','exists','both')
            assert len(node.args)==(1 if name=='neg' else 2)
            operation={'neg':self.negation,'exists':self.existential,'both':self.conjunction}[name]()
        return [[self.expression(a) for a in node.args],operation]

    @subroutine
    def axiom(self):
        bodies=[self.expression(e) for e in self.axiom_expressions]
        # Invalid gate must push truth; equality tests consume only copies.
        bodies[-1]=self.label('gate',[
            self.copy(self.s1,self.c),self.copy(self.s2,self.a),self.equal(self.data,self.s1,self.s2),
            self.if_decnz(self.data,[self.push(self.top,self.stack,0),'break_gate']),
            self.copy(self.s1,self.c),self.copy(self.s2,self.b),self.equal(self.data,self.s1,self.s2),
            self.if_decnz(self.data,[self.push(self.top,self.stack,0),'break_gate']),
            bodies[-1]])
        return self.choose(self.selector,bodies)

    @subroutine
    def command_axiom(self):
        return [self.divbase(self.u,self.selector,self.data,9),
            self.unpair(self.a,self.data,self.u),self.unpair(self.b,self.u,self.data),
            self.unpair(self.c,self.data,self.u),self.move(self.u,self.data),self.axiom(),
            [self.clear(r) for r in (self.a,self.b,self.c,self.u)]]

    @subroutine
    def command_generalize(self):
        return [self.pair(self.s1,self.data,self.top),self.scale(self.top,self.s1,4),
                self.top.inc,self.top.inc]

    @subroutine
    def command_mp(self):
        return [self.clear(self.data),self.pop(self.a,self.stack,0),self.divbase(self.data,self.selector,self.top,4),
            self.if_zero(self.selector,[self.unpair(self.b,self.c,self.data),
                self.equal(self.u,self.a,self.b),self.if_decnz(self.u,self.move(self.top,self.c))]),
            [self.clear(r) for r in (self.selector,self.data,self.a,self.b,self.c,self.u)]]

    @subroutine
    def command_drop(self):
        return [self.clear(self.data),self.clear(self.top),self.pop(self.top,self.stack,0)]

    @subroutine
    def theorem(self):
        return [self.copy(self.program,self.proof),self.while_decnz(self.program,[
            self.unpair(self.data,self.s1,self.program),self.move(self.program,self.s1),
            self.divbase(self.u,self.tag,self.data,4),self.move(self.data,self.u),
            self.choose(self.tag,[self.command_axiom(),self.command_generalize(),
                                  self.command_mp(),self.command_drop()])]),self.clear(self.stack)]

    @subroutine
    def require(self,register,value):
        return [[self.if_not_decnz(register,'break_record')]*value,
                self.if_nz(register,'break_record')]

    @subroutine
    def strip_negation(self):
        return [self.divbase(self.data,self.tag,self.top,4),self.require(self.tag,0),
                self.unpair(self.top,self.c,self.data),self.require(self.c,1)]

    @subroutine
    def strip_universal(self):
        return [self.divbase(self.data,self.tag,self.top,4),self.require(self.tag,2),
                self.unpair(self.a,self.top,self.data)]

    @subroutine
    def lookup(self,query):
        # Preserve env, return lookup value in query; missing names have 0.
        return [self.copy(self.c,self.env),self.label('lookup',[
            self.label('search',[self.if_zero(self.c,'break_search'),
                self.unpair(self.u,self.s1,self.c),self.move(self.c,self.s1),
                self.unpair(self.s1,self.s2,self.u),self.copy(self.u,query),
                self.equal(self.data,self.u,self.s1),self.if_decnz(self.data,[
                    self.clear(query),self.move(query,self.s2),self.clear(self.c),'break_lookup']),
                self.clear(self.s2),'continue_search']),self.clear(query)])]

    @subroutine
    def matrix_atom(self,kind):
        common=[self.unpair(self.a,self.b,self.data),self.lookup(self.a),self.lookup(self.b)]
        if kind==1:
            return [common,self.while_decnz(self.b,[self.divbase(self.s1,self.s2,self.a,2),
                self.move(self.a,self.s1),self.clear(self.s2)]),
                self.divbase(self.s1,self.s2,self.a,2),self.clear(self.s1),
                self.move(self.a,self.s2),self.push(self.a,self.program,0)]
        return [common,self.equal(self.u,self.a,self.b),self.push(self.u,self.program,0)]

    @subroutine
    def matrix_implication(self):
        return [self.unpair(self.a,self.b,self.data),self.u.inc,self.push(self.u,self.stack,1),
            self.scale(self.u,self.b,2),self.push(self.u,self.stack,1),
            self.scale(self.u,self.a,2),self.push(self.u,self.stack,1)]

    @subroutine
    def matrix_combine(self):
        return [self.pop(self.b,self.program,0),self.pop(self.a,self.program,0),
            self.if_zero(self.a,self.u.inc),self.if_nz(self.b,[self.clear(self.u),self.u.inc]),
            self.clear(self.a),self.clear(self.b),self.push(self.u,self.program,0)]

    @subroutine
    def matrix_enter(self):
        return [self.if_zero(self.top,[self.u.inc,self.push(self.u,self.program,0)]),
            self.if_nz(self.top,[self.divbase(self.data,self.selector,self.top,4),
                self.choose(self.selector,[self.matrix_implication(),self.matrix_atom(1),
                                          'break_record',self.matrix_atom(3)])])]

    @subroutine
    def matrix(self):
        return [self.scale(self.a,self.top,2),self.push(self.a,self.stack,1),
            self.while_decnz(self.stack,[self.unpair(self.a,self.s1,self.stack),
                self.move(self.stack,self.s1),self.divbase(self.top,self.tag,self.a,2),
                self.choose(self.tag,[self.matrix_enter(),self.matrix_combine()])]),
            self.pop(self.a,self.program,0),self.if_zero(self.a,self.bit.inc)]

    @subroutine
    def record(self):
        return [self.theorem(),self.copy(self.count,self.rank),self.copy(self.back,self.tuple),
            self.label('record',[self.while_decnz(self.count,[self.pop(self.b,self.back,1),
                self.choose(self.selector,[[self.strip_negation(),self.strip_universal(),
                    self.strip_negation(),self.selector.inc],self.strip_universal()]),
                self.pair(self.c,self.a,self.b),self.push(self.c,self.env,0)]),
                self.clear(self.selector),self.matrix()])]

    @subroutine
    def emit_natural(self,value):
        return [self.while_decnz(value,'emit.1'),'emit.0']

    @subroutine
    def main(self):
        work=(self.rest,self.count,self.back,self.top,self.stack,self.program,self.tag,
              self.data,self.a,self.b,self.c,self.u,self.selector,self.env,self.s1,self.s2)
        return [self.copy(self.rest,self.stage),self.unpair(self.rank,self.s1,self.rest),
            self.move(self.rest,self.s1),self.rank.inc,self.unpair(self.proof,self.s1,self.rest),
            self.move(self.rest,self.s1),self.copy(self.count,self.rank),
            self.while_decnz(self.count,[self.unpair(self.a,self.s1,self.rest),self.move(self.rest,self.s1),
                self.push(self.a,self.back,1)]),self.clear(self.rest),
            self.while_decnz(self.back,[self.unpair(self.a,self.s1,self.back),self.move(self.back,self.s1),
                self.push(self.a,self.tuple,1)]),self.record(),[self.clear(r) for r in work],
            self.emit_natural(self.rank),self.emit_natural(self.proof),
            self.while_decnz(self.tuple,[self.unpair(self.a,self.s1,self.tuple),self.move(self.tuple,self.s1),
                self.emit_natural(self.a)]),self.emit_natural(self.bit),self.stage.inc]

    def build_tree(self):
        self.main()
        self.reduce_to_cons()
        self.name_sequences()
        return self


def compile_direct(source,out):
    builder=Direct(source)
    builder.build_tree()
    builder.generate()
    labels={}
    for bit in '01':
        builder.tm.states['emit.'+bit,'0']=tm.Transition('1','R','1b.reg.prep_1')
        builder.tm.states['emit.'+bit,'1']=tm.Transition('0','L','6.break.0')
        labels['emit.'+bit,'1']=bit
    initial=build.counted_initializer(builder)
    builder.tm.symbols={'0','1'};builder.tm.gc()
    missing=totalize_silently(builder);builder.tm.gc()
    named={(q,int(r)):(int(t.write),t.direction,t.nextstate,labels.get((q,r),'-'))
           for (q,r),t in builder.tm.states.items()}
    root,measures=build.dag_measures(builder)
    meta=dict(initializer=initial,register_order=list(builder.registers),grammar_root=root,
        grammar={str(i):list(builder.sequences[i].seq) for i in sorted(builder.reachable())},
        grammar_names={str(i):builder.sequences[i].name for i in sorted(builder.reachable())},
        grammar_depth=measures[root][0],grammar_zero_depth=measures[root][1],
        totalized_rows=[[q,int(s)] for q,s in sorted(missing)],optimized=False,direct_events=True,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        implementation_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    rows,names=build.number_rows(named);meta['named_state_to_id']=names
    meta['state_ledger']=dict(Counter('initializer' if q.startswith('init.') else
        'grammar' if q in meta['grammar_names'].values() else
        'register-selection' if q.startswith(('2b.reg.','3.')) else
        'events' if q.startswith(('event.','emit.')) else 'engine-and-totalization' for q in names))
    raw=build.write_machine(out/'raw',rows,meta)
    reduced,certificate=build.exact_quotient(rows)
    certificate['source_table_sha256']=raw['table_sha256']
    best=build.write_machine(out/'quotient',reduced,dict(parent='raw',quotient=certificate,
        source_sha256=meta['source_sha256'],implementation_sha256=meta['implementation_sha256']))
    ledger=dict(raw=raw['states'],quotient=best['states'],registers=len(builder.registers),
        grammar=len(meta['grammar']),ledger=meta['state_ledger'],source_sha256=meta['source_sha256'],
        implementation_sha256=meta['implementation_sha256'],table_sha256=best['table_sha256'])
    (out/'ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
    return builder,ledger


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--source',type=Path,default=HERE/'source.py')
    args=parser.parse_args()
    builder,result=compile_direct(args.source.read_text(),args.out)
    print(json.dumps(result,sort_keys=True))
