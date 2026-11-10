#!/usr/bin/env python3
"""Combined choice/binder syntax over the paid numeric-environment support.

H(A,B)(E) = not A(0::E) or exists x not B(x::E).
Every active node binds and flips sign; observer ownership then alternates
automatically. This is distinct from the concurrent309 finite-table schedule.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
import bounded
from TMBuilder import subroutine
p=bounded.p


class HGame(bounded.ElevenRegisterBound):
    @subroutine
    def decode_top(self):
        return [self.divbase(self.data,self.selector,self.top,2),
                self.move(self.top,self.data)]

    @subroutine
    def h_node(self):
        return [self.clear(self.selector),self.unpair(self.selector,self.c,self.top),
            self.label('branch',[
                self.if_decnz(self.stack,[self.move(self.top,self.c),
                    self.clear(self.selector),'break_branch']),
                self.move(self.top,self.selector),self.clear(self.c)]),
            self.pair(self.c,self.stack,self.env),self.move(self.env,self.c),
            self.toggle(self.owner),self.decode_top()]

    @subroutine
    def game_step(self):
        return [self.if_nz(self.selector,self.h_node()),self.clear(self.stack)]

    @subroutine
    def game_terminal(self):
        return [self.if_nz(self.selector,self.finish_true()),
            self.move(self.data,self.top),self.matrix_atom(1),
            self.if_decnz(self.owner,self.toggle(self.count))]

    @subroutine
    def main(self):
        work=(self.rest,self.top,self.env,self.stack,self.a,self.b,self.c,self.s1,self.owner)
        return [self.copy(self.rest,self.stage),self.unpair(self.count,self.s1,self.rest),
            self.move(self.rest,self.s1),self.count.inc,self.emit_preserving(self.count),
            self.formula_index(),self.label('record',[
                self.take_coordinate(),self.clear(self.stack),
                self.take_coordinate(),self.move(self.env,self.stack),
                self.take_coordinate(),self.move(self.b,self.stack),
                self.take_coordinate(),self.prepare_predicate(),
                self.if_nz(self.owner,[self.take_coordinate(),self.clear(self.stack)]),
                self.decode_top(),
                self.while_decnz(self.count,[self.emit_coordinate(),self.game_step()]),
                self.game_terminal()]),
            self.toggle(self.count),[self.clear(r) for r in work],
            self.emit_natural(self.count),self.stage.inc]


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    if args.out.exists():raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(HGame,args.out)[1],indent=2))
