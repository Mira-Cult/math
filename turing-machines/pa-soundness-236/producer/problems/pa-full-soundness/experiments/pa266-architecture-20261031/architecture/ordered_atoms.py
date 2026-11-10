#!/usr/bin/env python3
"""Paid H syntax with ordered membership operands and relative lookup distance.

Even formula 2*P(j,d) means bit(E[j+d],E[j]); H is unchanged. This changes
numeric formula meaning, so use its own reference and coverage theorem.
Every atomic environment lookup is terminal and may consume env.
"""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parents[1] / 'pa576-architecture-20261031'
sys.path[:0] = [str(OLD / 'architecture'), str(OLD)]
import paired_polarity
from TMBuilder import subroutine

p = paired_polarity.p


class OrderedAtoms(paired_polarity.PairedPolarity):
    @subroutine
    def scan_to_a(self):
        # Consume b and a; return selected head c and its following tail scratch.
        return [
            self.unpair(self.c, self.scratch, self.b),
            self.while_decnz(self.a, [
                self.clear(self.c), self.move(self.b, self.scratch),
                self.unpair(self.c, self.scratch, self.b),
            ]),
        ]

    @subroutine
    def atom_bit(self):
        return [
            self.unpair(self.c, self.scratch, self.b),
            self.move(self.a, self.c), self.move(self.top, self.scratch),
            self.label('ordered_atom', [
                self.if_not_decnz(self.top, [self.clear(self.a), 'break_ordered_atom']),
                self.move(self.b, self.env), self.scan_to_a(), self.move(self.env, self.c),
                self.move(self.b, self.scratch), self.move(self.a, self.top), self.scan_to_a(),
                self.clear(self.scratch), self.move(self.b, self.c), self.move(self.a, self.env),
                self.bit_b_a(),
            ]),
        ]


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(OrderedAtoms, args.out)[1], indent=2))
