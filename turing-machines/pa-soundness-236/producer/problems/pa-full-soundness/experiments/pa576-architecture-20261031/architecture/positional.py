#!/usr/bin/env python3
"""Paid phase/output compositions over the frozen positional game source."""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent))
import producer as p
from TMBuilder import subroutine


class CachedPositional(p.PositionalGame):
    @subroutine
    def decode_top(self):
        return [self.divbase(self.data,self.selector,self.top,4),
                self.move(self.top,self.data)]

    @subroutine
    def game_implication(self):
        return self.if_zero(self.owner,[
            self.unpair(self.a,self.b,self.top),self.label('branch',[
                self.if_nz(self.stack,[self.move(self.top,self.b),'break_branch']),
                self.move(self.top,self.a),self.toggle(self.polarity),
                self.toggle(self.owner)]),self.decode_top()])

    @subroutine
    def game_universal(self):
        # The cached universal payload is already the full child formula.
        return self.if_nz(self.owner,[self.clear(self.selector),
            self.pair(self.c,self.stack,self.env),self.move(self.env,self.c),
            self.decode_top()])

    @subroutine
    def game_step(self):
        return [self.choose(self.selector,[
            self.if_nz(self.top,self.game_implication()),
            self.selector.inc,
            [[self.selector.inc]*2,self.game_universal()],
            [self.selector.inc]*3]),
            [self.clear(r) for r in (self.stack,self.a,self.b,self.c,self.u,self.s1,self.s2)],
            self.toggle(self.owner)]

    @subroutine
    def game_terminal(self):
        return [self.choose(self.selector,[
            [self.if_nz(self.top,self.finish_true()),self.count.inc],
            [self.move(self.data,self.top),self.matrix_atom(1)],
            self.finish_true(),
            [self.move(self.data,self.top),self.matrix_atom(3)]]),
            self.if_decnz(self.polarity,self.toggle(self.count))]

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
                self.take_coordinate(),self.prepare_predicate(),self.decode_top(),
                self.while_decnz(self.count,[self.emit_coordinate(),self.game_step()]),
                self.game_terminal()]),
            self.toggle(self.count),[self.clear(r) for r in work],
            self.emit_natural(self.count),self.stage.inc]


class PositionalOutput:
    @subroutine
    def emit_preserving(self,value):
        return [self.while_decnz(value,['emit.1',self.scratch.inc]),
                'emit.0',self.move(value,self.scratch)]

    @subroutine
    def emit_coordinate(self):
        return [self.unpair(self.stack,self.s1,self.rest),self.move(self.rest,self.s1),
                self.emit_preserving(self.stack)]

    @subroutine
    def formula_index(self):
        return [self.unpair(self.top,self.s1,self.rest),self.move(self.rest,self.s1),
                self.emit_preserving(self.top)]

    @subroutine
    def main(self):
        work=(self.rest,self.top,self.env,self.stack,self.a,self.b,self.c,self.u,
              self.selector,self.s1,self.s2,self.owner,self.polarity)
        return [self.copy(self.rest,self.stage),self.unpair(self.count,self.s1,self.rest),
            self.move(self.rest,self.s1),self.count.inc,self.emit_preserving(self.count),
            self.formula_index(),
            self.label('record',[
                self.take_coordinate(),self.clear(self.stack),
                self.take_coordinate(),self.move(self.env,self.stack),
                self.take_coordinate(),self.move(self.b,self.stack),
                self.take_coordinate(),self.prepare_predicate(),
                self.decode_top() if self.cached else [],
                self.while_decnz(self.count,[self.emit_coordinate(),self.game_step()]),
                self.game_terminal()]),
            self.toggle(self.count),[self.clear(r) for r in work],
            self.emit_natural(self.count),self.stage.inc]


class FusedPositional(PositionalOutput,p.PositionalGame):
    cached=False


class FusedCachedPositional(PositionalOutput,CachedPositional):
    cached=True


VARIANTS={'cached':CachedPositional,'output':FusedPositional,
          'cached-output':FusedCachedPositional}

def run(out):
    out=Path(out)
    if out.exists():raise ValueError('Fresh output directory required')
    for name,cls in VARIANTS.items():
        _,ledger,_=p.opt.compile_candidate(cls,out/name)
        print(name,json.dumps(ledger),flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args();run(args.out)
