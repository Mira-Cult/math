#!/usr/bin/env python3
"""Price syntax decoding using only the already paid Cantor inverse.

Codes: true=0; all(g)=P(0,g); member(i,j)=P(1,P(i,j));
imp(l,r)=P(l+2,r). Universal true aliases true. This changes addresses and
needs its own syntax-coverage theorem; no equal-record claim to ternary codes.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
import reductions
from TMBuilder import subroutine

p=reductions.p


class PairedSyntax(reductions.MembershipOnlyGame):
    @subroutine
    def decode_top(self):
        return [self.unpair(self.selector,self.data,self.top),
                self.move(self.top,self.data)]

    @subroutine
    def game_implication(self):
        # selector already holds the left child after two dispatch decrements.
        return self.label('ownership',[
            self.if_nz(self.owner,[[self.selector.inc]*2,'break_ownership']),
            self.label('branch',[
                self.if_nz(self.stack,[self.clear(self.selector),'break_branch']),
                self.clear(self.top),self.move(self.top,self.selector),
                self.toggle(self.polarity),self.toggle(self.owner)]),
            self.decode_top()])

    @subroutine
    def game_universal(self):
        return self.if_nz(self.owner,[
            self.pair(self.c,self.stack,self.env),self.move(self.env,self.c),
            self.decode_top()])

    @subroutine
    def game_step(self):
        return [self.label('dispatch',[
            self.if_not_decnz(self.selector,[
                self.if_nz(self.top,self.game_universal()),'break_dispatch']),
            self.if_not_decnz(self.selector,[self.selector.inc,'break_dispatch']),
            self.game_implication()]),
            [self.clear(r) for r in (self.stack,self.a,self.b,self.c,self.u,self.s1,self.s2)],
            self.toggle(self.owner)]

    @subroutine
    def game_terminal(self):
        return [self.label('terminal',[
            self.if_not_decnz(self.selector,[
                self.if_nz(self.top,self.finish_true()),self.count.inc,'break_terminal']),
            self.if_not_decnz(self.selector,[
                self.move(self.data,self.top),self.matrix_atom(1),'break_terminal']),
            self.finish_true()]),
            self.if_decnz(self.polarity,self.toggle(self.count))]


def run(out):
    out=Path(out)
    if out.exists():raise ValueError('Fresh output directory required')
    _,ledger,_=p.opt.compile_candidate(PairedSyntax,out)
    return ledger

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args();print(json.dumps(run(args.out),indent=2))
