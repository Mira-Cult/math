#!/usr/bin/env python3
"""Paid strictly ordered atom language: 2*P(j,g) means bit(E[j+g+1],E[j])."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import ordered_atoms
from TMBuilder import subroutine

p = ordered_atoms.p


class StrictAtoms(ordered_atoms.OrderedAtoms):
    @subroutine
    def atom_bit(self):
        return [
            self.unpair(self.c, self.scratch, self.b),
            self.move(self.a, self.c), self.move(self.top, self.scratch),
            self.move(self.b, self.env), self.scan_to_a(), self.move(self.env, self.c),
            self.move(self.b, self.scratch), self.move(self.a, self.top), self.scan_to_a(),
            self.clear(self.scratch), self.move(self.b, self.c), self.move(self.a, self.env),
            self.bit_b_a(),
        ]


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(StrictAtoms, args.out)[1], indent=2))
