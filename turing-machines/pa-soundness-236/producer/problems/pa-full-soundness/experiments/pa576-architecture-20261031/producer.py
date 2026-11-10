#!/usr/bin/env python3
"""Positional finite games for the compact comprehension basis.

This is newly implemented source, not recovery of the reported lost PA279.
The source/coverage proof is separate from the inherited physical runtime.
"""
from __future__ import annotations
import argparse, hashlib, json, sys
from pathlib import Path

ROOT=Path(__file__).resolve().parent
PA804=ROOT.parent/'pa804-continuation'
sys.path.insert(0,str(PA804))
import optimize as opt
import grammar_search as gs
from TMBuilder import subroutine


class PositionalGame(opt.direct.Direct):
    """No constructed axiom, named binders, or associative environment.

    Formula codes: 0=true; 4P(a,b)=implication; 4P(i,j)+1=membership;
    4body+2=universal; 4P(i,j)+3=equality.  Variables are de Bruijn indices.
    Every natural is admitted. Missing positional environment entries are zero.
    """
    def __init__(self,source):
        opt.build.OmegaBuilder.__init__(self,'def main():\n    while True:\n        emit0()\n',share=False)
        self.reference_source=source
        for name in ('stage','rest','count','top','env','stack','a','b','c','u',
                     'selector','s1','s2','owner','polarity'):
            setattr(self,name,self.reg('k.'+name))
        self.data=self.c
        self.program=self.count

    @subroutine
    def toggle(self,r):
        return self.choose(r,[r.inc,[]])

    @subroutine
    def emit_coordinate(self):
        # stack=s1=a=0 on entry and after the caller consumes this move.
        return [self.unpair(self.stack,self.s1,self.rest),self.move(self.rest,self.s1),
                self.copy(self.a,self.stack),self.emit_natural(self.a)]

    @subroutine
    def finish_true(self):
        return [self.clear(self.stack),self.clear(self.a),
                self.while_decnz(self.count,[self.emit_coordinate(),self.clear(self.stack)]),
                self.count.inc,'break_record']

    @subroutine
    def take_coordinate(self):
        return [self.if_not_decnz(self.count,self.finish_true()),self.emit_coordinate()]

    @subroutine
    def lookup(self,query):
        # env preserved, query replaced by env[query]. c,u,s1 all restored zero.
        return [self.copy(self.c,self.env),
            self.while_decnz(query,[self.unpair(self.u,self.s1,self.c),
                self.move(self.c,self.s1),self.clear(self.u)]),
            self.unpair(query,self.s1,self.c),self.clear(self.s1)]

    @subroutine
    def bit(self,value,index):
        # Destructively replace value by bit(value,index); index/s1/s2 -> zero.
        return [self.while_decnz(index,[self.divbase(self.s1,self.s2,value,2),
                    self.move(value,self.s1),self.clear(self.s2)]),
                self.divbase(self.s1,self.s2,value,2),self.clear(self.s1),
                self.move(value,self.s2)]

    @subroutine
    def prepare_predicate(self):
        # top=formula, env=packed assignment, b=C, stack=y.
        # env's first two entries are A,B.  Select phi, not phi, or true.
        return [self.copy(self.u,self.stack),self.bit(self.b,self.u),
            self.label('selected',[
                self.if_decnz(self.b,'break_selected'),
                self.copy(self.c,self.env),self.unpair(self.a,self.b,self.c),
                self.clear(self.b),self.copy(self.u,self.stack),self.bit(self.a,self.u),
                self.if_decnz(self.a,[self.polarity.inc,self.owner.inc,'break_selected']),
                self.copy(self.c,self.env),self.unpair(self.a,self.b,self.c),self.clear(self.a),
                self.unpair(self.a,self.c,self.b),self.clear(self.c),
                self.copy(self.b,self.stack),self.equal(self.u,self.a,self.b),
                self.if_not_decnz(self.u,self.finish_true()),
                self.polarity.inc,self.owner.inc]),
            self.pair(self.c,self.stack,self.env),self.move(self.env,self.c)]

    @subroutine
    def game_implication(self):
        # owner=parity xor polarity; implication belongs to existential iff 0.
        return self.if_zero(self.owner,[self.clear(self.top),
            self.unpair(self.a,self.b,self.data),self.label('branch',[
                self.if_nz(self.stack,[self.move(self.top,self.b),'break_branch']),
                self.move(self.top,self.a),self.toggle(self.polarity),self.toggle(self.owner)])])

    @subroutine
    def game_universal(self):
        return self.if_nz(self.owner,[self.clear(self.top),self.move(self.top,self.data),
            self.pair(self.c,self.stack,self.env),self.move(self.env,self.c)])

    @subroutine
    def game_step(self):
        return [self.if_nz(self.top,[self.copy(self.u,self.top),
                self.divbase(self.data,self.selector,self.u,4),
                self.choose(self.selector,[self.game_implication(),[],self.game_universal(),[]])]),
            [self.clear(r) for r in (self.stack,self.a,self.b,self.c,self.u,self.s1,self.s2)],
            self.toggle(self.owner)]

    @subroutine
    def lookup_both(self):
        return [self.unpair(self.a,self.b,self.data),self.lookup(self.a),
            self.move(self.stack,self.a),self.move(self.a,self.b),self.lookup(self.a),
            self.move(self.b,self.a),self.move(self.a,self.stack)]

    @subroutine
    def matrix_atom(self,kind):
        return [self.lookup_both(),
            [self.bit(self.a,self.b),self.move(self.count,self.a)] if kind==1
            else self.equal(self.count,self.a,self.b)]

    @subroutine
    def game_terminal(self):
        return [self.if_zero(self.top,self.count.inc),
            self.if_nz(self.top,[self.divbase(self.data,self.selector,self.top,4),
                self.choose(self.selector,[self.finish_true(),self.matrix_atom(1),
                                          self.finish_true(),self.matrix_atom(3)])]),
            self.if_decnz(self.polarity,self.toggle(self.count))]

    @subroutine
    def formula_index(self):
        return [self.unpair(self.top,self.s1,self.rest),self.move(self.rest,self.s1),
                self.copy(self.a,self.top),self.emit_natural(self.a)]

    @subroutine
    def main(self):
        work=(self.rest,self.top,self.env,self.stack,self.a,self.b,self.c,self.u,
              self.selector,self.s1,self.s2,self.owner,self.polarity)
        return [self.copy(self.rest,self.stage),self.unpair(self.count,self.s1,self.rest),
            self.move(self.rest,self.s1),self.count.inc,
            self.copy(self.a,self.count),self.emit_natural(self.a),
            self.formula_index(),
            self.label('record',[
                self.take_coordinate(),self.clear(self.stack),
                self.take_coordinate(),self.move(self.env,self.stack),
                self.take_coordinate(),self.move(self.b,self.stack),
                self.take_coordinate(),self.prepare_predicate(),
                self.while_decnz(self.count,[self.emit_coordinate(),self.game_step()]),
                self.game_terminal()]),
            # Every exit has emitted all rank coordinates and count is truth.
            self.toggle(self.count),[self.clear(r) for r in work],
            self.emit_natural(self.count),self.stage.inc]

    def build_tree(self):
        super().build_tree()
        self.reference_graph=gs.graph(self)
        self.breakout_common_subsequences();self.reduce_to_cons();self.name_sequences()
        assert gs.graph(self)==self.reference_graph
        return self


def build(out,cls=PositionalGame):
    out=Path(out)
    if out.exists():raise ValueError('Output must be fresh')
    b,ledger,rows=opt.compile_candidate(cls,out/'machine')
    paths=[Path(__file__).resolve()]+[PA804/x for x in (
        'optimize.py','grammar_search.py','baseline/code/compact/source.py',
        'baseline/code/compact/direct.py','baseline/code/build.py',
        'baseline/code/shared/backend.py','baseline/code/shared/vendor/TMBuilder.py',
        'baseline/code/shared/vendor/tm.py')]
    paths += [ROOT.parent.parent/'recovery/compact-successor'/x for x in
              ('manuscripts/omega-semantics.md','code/trace_semantics.py')]
    (out/'input-sha256.json').write_text(json.dumps({str(x.relative_to(ROOT.parents[3])):
        hashlib.sha256(x.read_bytes()).hexdigest() for x in paths},sort_keys=True,indent=2)+'\n')
    graph=gs.graph(b)
    (out/'grammar-certificate.json').write_text(json.dumps(dict(
        reference_graph=b.reference_graph,candidate_graph=graph,graph_sha256=gs.digest(graph),
        primitive_occurrences=len(graph),control_edges=sum(len(row)-1 for row in graph),
        scope='Exact factoring of the new positional producer, not equivalence to old axiom-index records.'),
        sort_keys=True,indent=2)+'\n')
    return b,ledger,rows

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);args=p.parse_args()
    print(json.dumps(build(args.out)[1],indent=2))
