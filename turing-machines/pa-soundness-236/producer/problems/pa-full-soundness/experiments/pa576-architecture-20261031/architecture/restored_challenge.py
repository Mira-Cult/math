#!/usr/bin/env python3
"""Restore the rank and both challenge uses in one successful comparator pass."""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
import closed_table
from TMBuilder import subroutine

p = closed_table.p


class RestoredChallenge(closed_table.ClosedFiniteTable):
    @subroutine
    def prefix(self):
        return [
            self.take(), self.move(self.b, self.a),
            self.take(),
            self.while_decnz(self.a, [
                self.if_not_decnz(self.count, [self.move(self.count, self.c), self.finish_true()]),
                self.c.inc,
            ]),
            self.while_decnz(self.c, [self.count.inc, self.a.inc, self.owner.inc]),
            self.bit_b_a(), self.move(self.a, self.owner), self.bind_a(),
            self.if_not_decnz(self.b, self.owner.inc),
            self.if_nz(self.owner, [self.take(), self.clear(self.a)]),
        ]


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(RestoredChallenge, args.out)[1], indent=2))
