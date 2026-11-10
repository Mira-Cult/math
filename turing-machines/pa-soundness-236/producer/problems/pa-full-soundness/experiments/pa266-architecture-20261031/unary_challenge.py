#!/usr/bin/env python3
"""Grow/stop universal challenges; every grow spends a coordinate pair."""
from __future__ import annotations
import argparse
import json
import spent_rank
from TMBuilder import subroutine
p = spent_rank.p


class UnaryChallenge(spent_rank.paired_polarity.PairedPolarity):
    @subroutine
    def unsigned_prefix(self):
        return [self.take(), self.move(self.b, self.a),
            self.label('challenge', [
                self.take(),
                self.if_not_decnz(self.a, 'break_challenge'),
                self.clear(self.a), self.env.inc,
                self.divbase(self.c, self.scratch, self.b, 2),
                self.move(self.b, self.c), self.clear(self.scratch),
                self.take(), self.clear(self.a), 'continue_challenge',
            ]),
            self.bit_b_a(), self.move(self.a, self.env), self.bind_a()]


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=spent_rank.Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(UnaryChallenge, args.out)[1], indent=2))
