#!/usr/bin/env python3
"""Two-coordinate caller removes the separate polarity register."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import paired_syntax
from TMBuilder import subroutine

p=paired_syntax.p


class PairedSingleSign(paired_syntax.PairedSyntax):
    def reg(self,name):
        return super().reg('k.owner' if name=='k.polarity' else name)

    @subroutine
    def prepare_predicate(self):
        return [self.copy(self.u,self.stack),self.bit(self.b,self.u),
            self.label('selected',[
                self.if_decnz(self.b,'break_selected'),
                self.copy(self.c,self.env),self.unpair(self.a,self.b,self.c),
                self.clear(self.b),self.copy(self.u,self.stack),self.bit(self.a,self.u),
                self.if_not_decnz(self.a,self.finish_true()),self.owner.inc]),
            self.pair(self.c,self.stack,self.env),self.move(self.env,self.c)]

    @subroutine
    def game_implication(self):
        return self.label('ownership',[
            self.if_nz(self.owner,[[self.selector.inc]*2,'break_ownership']),
            self.label('branch',[
                self.if_nz(self.stack,[self.clear(self.selector),'break_branch']),
                self.clear(self.top),self.move(self.top,self.selector),self.toggle(self.owner)]),
            self.decode_top()])

    @subroutine
    def game_terminal(self):
        return [self.label('terminal',[
            self.if_not_decnz(self.selector,[
                self.if_nz(self.top,self.finish_true()),self.count.inc,'break_terminal']),
            self.if_not_decnz(self.selector,[
                self.move(self.data,self.top),self.matrix_atom(1),'break_terminal']),
            self.finish_true()]),
            self.if_decnz(self.owner,self.toggle(self.count))]

    @subroutine
    def main(self):
        work=(self.rest,self.top,self.env,self.stack,self.a,self.b,self.c,self.u,
              self.selector,self.s1,self.s2,self.owner)
        return [self.copy(self.rest,self.stage),self.unpair(self.count,self.s1,self.rest),
            self.move(self.rest,self.s1),self.count.inc,self.emit_preserving(self.count),
            self.formula_index(),self.label('record',[
                self.take_coordinate(),self.clear(self.stack),
                self.take_coordinate(),self.move(self.env,self.stack),
                self.take_coordinate(),self.move(self.b,self.stack),
                self.take_coordinate(),self.prepare_predicate(),self.decode_top(),
                self.label('game_tail',[
                    self.while_decnz(self.count,[
                        self.emit_coordinate(),self.game_step(),
                        self.if_not_decnz(self.count,[self.toggle(self.owner),'break_game_tail']),
                        self.emit_coordinate(),self.game_step()])]),
                self.game_terminal()]),
            self.toggle(self.count),[self.clear(r) for r in work],
            self.emit_natural(self.count),self.stage.inc]


def run(out):
    out=Path(out)
    if out.exists():raise ValueError('Fresh output directory required')
    _,ledger,_=p.opt.compile_candidate(PairedSingleSign,out)
    return ledger

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args();print(json.dumps(run(args.out),indent=2))
