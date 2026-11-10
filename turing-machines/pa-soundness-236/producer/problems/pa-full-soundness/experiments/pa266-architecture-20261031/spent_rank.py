#!/usr/bin/env python3
"""Paid finite-table family: consume coordinate pairs instead of restoring rank.

New finite records, unchanged addressed observer.  The initial environment code
P(y,0) is also the finite support price; its ignored pairs preserve ownership.
"""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'pa576-architecture-20261031'
sys.path[:0] = [str(OLD / 'architecture'), str(OLD)]
import paired_polarity
from TMBuilder import subroutine
p = paired_polarity.p


class SpentRank(paired_polarity.PairedPolarity):
    @subroutine
    def unsigned_prefix(self):
        return [self.take(), self.move(self.b, self.a), self.take(),
                self.copy(self.env, self.a), self.bit_b_a(),
                self.move(self.a, self.env), self.bind_a()]

    @subroutine
    def pay_pairs(self):
        return [self.copy(self.b, self.env), self.while_decnz(self.b, [
            self.take(), self.clear(self.a), self.take(), self.clear(self.a)])]

    @subroutine
    def main(self):
        work = (self.rest, self.env, self.a, self.b, self.c, self.scratch)
        return [
            self.copy(self.rest, self.stage), self.unpair(self.a, self.c, self.rest),
            self.move(self.rest, self.c), self.a.inc, self.emit_preserving(self.a),
            self.move(self.count, self.a), self.formula_index(),
            self.label('record', [
                self.unsigned_prefix(),
                self.label('select_phase', [
                    self.if_decnz(self.b, [self.pay_pairs(), 'break_select_phase']),
                    self.pay_pairs(), self.take(), self.clear(self.a), self.signed_step(True),
                ]),
                self.label('walk_pairs', [self.signed_step(False), self.signed_step(True), 'continue_walk_pairs']),
            ]),
            self.clear(self.a), self.clear(self.c),
            self.while_decnz(self.count, [self.emit_coordinate(), self.clear(self.a)]),
            [self.clear(r) for r in work], self.emit_natural(self.top), self.stage.inc,
        ]


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(SpentRank, args.out)[1], indent=2))
