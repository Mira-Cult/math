#!/usr/bin/env python3
"""Ten-cell H consumer: direct path traversal, early atoms, shared bit/binding.

Same finite record function as h_game.HGame. Remaining address fields are
drained after an atom; formula storage then holds the computed rejection bit.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
import h_game
from TMBuilder import subroutine
p=h_game.p


class HWalk(p.opt.direct.Direct):
    def __init__(self,source):
        p.opt.build.OmegaBuilder.__init__(self,'def main():\n    while True:\n        emit0()\n',share=False)
        self.reference_source=source
        for name in ('stage','rest','count','top','env','a','b','c','owner'):
            setattr(self,name,self.reg('k.'+name))

    @subroutine
    def toggle(self,x):
        return self.label('toggle',[[x.decnz,'break_toggle'],x.inc])

    @subroutine
    def emit_preserving(self,value):
        return [self.while_decnz(value,['emit.1',self.scratch.inc]),
                'emit.0',self.move(value,self.scratch)]

    @subroutine
    def emit_coordinate(self):
        # a,c,scratch zero; b is a possibly live H payload.
        return [self.unpair(self.a,self.c,self.rest),self.move(self.rest,self.c),
                self.emit_preserving(self.a)]

    @subroutine
    def formula_index(self):
        return [self.unpair(self.top,self.c,self.rest),self.move(self.rest,self.c),
                self.emit_preserving(self.top)]

    @subroutine
    def finish_true(self):
        return [self.clear(self.top),'break_record']

    @subroutine
    def take(self):
        return [self.if_not_decnz(self.count,self.finish_true()),self.emit_coordinate()]

    @subroutine
    def bit_b_a(self):
        # b is set, a is index; c and copy scratch are zero at both boundaries.
        return [self.while_decnz(self.a,[self.divbase(self.c,self.scratch,self.b,2),
                    self.move(self.b,self.c),self.clear(self.scratch)]),
                self.divbase(self.c,self.scratch,self.b,2),self.clear(self.c),
                self.move(self.b,self.scratch)]

    @subroutine
    def bind_a(self):
        return [self.pair(self.c,self.a,self.env),self.move(self.env,self.c)]

    @subroutine
    def prefix(self):
        return [self.take(),self.clear(self.a),
            self.take(),self.move(self.env,self.a),
            self.take(),self.move(self.b,self.a),
            self.take(),self.copy(self.owner,self.a),self.bit_b_a(),
            self.label('selected',[
                self.if_decnz(self.b,'break_selected'),
                self.copy(self.c,self.env),self.copy(self.a,self.owner),
                self.while_decnz(self.a,self.if_not_decnz(self.c,self.finish_true())),
                self.clear(self.c),self.b.inc]),
            self.move(self.a,self.owner),self.bind_a(),self.move(self.owner,self.b),
            self.if_nz(self.owner,[self.take(),self.clear(self.a)])]

    @subroutine
    def lookup_a(self):
        return [self.copy(self.b,self.env),
            self.while_decnz(self.a,[self.unpair(self.c,self.scratch,self.b),
                self.move(self.b,self.scratch),self.clear(self.c)]),
            self.unpair(self.a,self.scratch,self.b),self.clear(self.scratch)]

    @subroutine
    def h_node(self):
        return [self.take(),self.unpair(self.top,self.c,self.b),
            self.label('branch',[
                self.if_decnz(self.a,[self.clear(self.top),self.move(self.top,self.c),'break_branch']),
                self.clear(self.c)]),
            self.bind_a(),self.toggle(self.owner),'continue_walk']

    @subroutine
    def atom(self):
        return [self.unpair(self.a,self.top,self.b),self.lookup_a(),
            self.move(self.c,self.a),self.move(self.a,self.top),self.move(self.top,self.c),
            self.lookup_a(),self.move(self.b,self.top),self.bit_b_a(),
            self.if_zero(self.owner,self.toggle(self.b)),self.move(self.top,self.b)]

    @subroutine
    def walk(self):
        return self.label('walk',[
            self.divbase(self.b,self.c,self.top,2),
            self.if_decnz(self.c,self.h_node()),self.atom()])

    @subroutine
    def main(self):
        work=(self.rest,self.env,self.a,self.b,self.c,self.owner,self.scratch)
        return [self.copy(self.rest,self.stage),self.unpair(self.count,self.c,self.rest),
            self.move(self.rest,self.c),self.count.inc,self.emit_preserving(self.count),
            self.formula_index(),self.label('record',[self.prefix(),self.walk()]),
            self.clear(self.a),self.clear(self.c),
            self.while_decnz(self.count,[self.emit_coordinate(),self.clear(self.a)]),
            [self.clear(r) for r in work],self.emit_natural(self.top),self.stage.inc]

    def build_tree(self):
        super().build_tree();self.reference_graph=p.gs.graph(self)
        self.breakout_common_subsequences();self.reduce_to_cons();self.name_sequences()
        assert p.gs.graph(self)==self.reference_graph
        return self


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    if args.out.exists():raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(HWalk,args.out)[1],indent=2))
