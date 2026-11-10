#!/usr/bin/env python3
"""Formula tags folded into Cantor pairing; atoms also consume one slot.

f=P(0,P(i,j)) is bit(env[i],env[j]); f=P(A+1,B) is H(A,B).
All codes are admitted, children strictly decrease, and cutoff is optimistic.
"""
from __future__ import annotations
import argparse
import json
import unary_challenge
from TMBuilder import subroutine
p = unary_challenge.p


class CantorTagged(unary_challenge.spent_rank.paired_polarity.PairedPolarity):
    @subroutine
    def h_step(self):
        return [self.label('branch', [
            self.if_decnz(self.a, [self.clear(self.c), self.move(self.c, self.scratch), 'break_branch']),
            self.clear(self.scratch),
        ]), self.move(self.top, self.c), self.bind_a()]

    @subroutine
    def signed_step(self, negative):
        return [self.move(self.b, self.top), self.take(),
            self.unpair(self.c, self.scratch, self.b),
            self.label('step', [
                self.if_decnz(self.c, [self.h_step(), 'break_step']),
                self.clear(self.a), self.move(self.b, self.scratch), self.atom_bit(),
                [] if negative else self.toggle(self.b),
                self.move(self.top, self.b), 'break_record',
            ])]


class UnaryCantor(CantorTagged, unary_challenge.UnaryChallenge):
    pass


CLASSES = {c.__name__: c for c in (CantorTagged, UnaryCantor)}
if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=unary_challenge.spent_rank.Path, required=True)
    parser.add_argument('--class-name', choices=CLASSES, required=True)
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(CLASSES[args.class_name], args.out)[1], indent=2))
