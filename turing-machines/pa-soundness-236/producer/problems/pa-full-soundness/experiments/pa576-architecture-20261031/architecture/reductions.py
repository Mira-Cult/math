#!/usr/bin/env python3
"""Complete support-only and membership-only positional game producers.

The new source families need the separately authored basis equivalences.
These are endpoint refinements, not the old ordered finite-rank records.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
import positional
from TMBuilder import subroutine

p=positional.p


class SupportOnlyGame(positional.FusedCachedPositional):
    """Interval comprehension with only a support set, no outside point."""
    @subroutine
    def prepare_predicate(self):
        # top=f, env=E with support A=head(E), b=C, stack=y.
        return [self.copy(self.u,self.stack),self.bit(self.b,self.u),
            self.label('selected',[
                self.if_decnz(self.b,'break_selected'),
                self.copy(self.c,self.env),self.unpair(self.a,self.b,self.c),
                self.clear(self.b),self.copy(self.u,self.stack),self.bit(self.a,self.u),
                self.if_not_decnz(self.a,self.finish_true()),
                self.polarity.inc,self.owner.inc]),
            self.pair(self.c,self.stack,self.env),self.move(self.env,self.c)]


class MembershipOnlyGame(SupportOnlyGame):
    """Ternary syntax: implication, membership and unnamed universal only."""
    @subroutine
    def decode_top(self):
        return [self.divbase(self.data,self.selector,self.top,3),
                self.move(self.top,self.data)]

    @subroutine
    def game_step(self):
        return [self.choose(self.selector,[
            self.if_nz(self.top,self.game_implication()),
            self.selector.inc,
            [[self.selector.inc]*2,self.game_universal()]]),
            [self.clear(r) for r in (self.stack,self.a,self.b,self.c,self.u,self.s1,self.s2)],
            self.toggle(self.owner)]

    @subroutine
    def game_terminal(self):
        return [self.choose(self.selector,[
            [self.if_nz(self.top,self.finish_true()),self.count.inc],
            [self.move(self.data,self.top),self.matrix_atom(1)],
            self.finish_true()]),
            self.if_decnz(self.polarity,self.toggle(self.count))]


VARIANTS={'support-only':SupportOnlyGame,'membership-only':MembershipOnlyGame}

def run(out):
    out=Path(out)
    if out.exists():raise ValueError('Fresh output directory required')
    for name,cls in VARIANTS.items():
        _,ledger,_=p.opt.compile_candidate(cls,out/name)
        print(name,json.dumps(ledger),flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args();run(args.out)
