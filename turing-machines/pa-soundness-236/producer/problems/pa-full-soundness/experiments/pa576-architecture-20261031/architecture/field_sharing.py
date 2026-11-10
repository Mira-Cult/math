#!/usr/bin/env python3
"""Share the complete unpair/output interface across all emitted input fields.

This changes only HWalk's physical source calling convention. Rank, formula
index and tuple coordinate all decode into a, with c as tail scratch; the
first two callers pay a destructive move into count or top. The exact ordered
record stream and the aligned-prefix cutoff are unchanged.
"""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
import h_walk
from TMBuilder import subroutine

p = h_walk.p


class HFieldSharing(h_walk.HWalk):
    @subroutine
    def formula_index(self):
        return [self.emit_coordinate(), self.move(self.top, self.a)]

    @subroutine
    def main(self):
        work = (self.rest, self.env, self.a, self.b, self.c, self.owner, self.scratch)
        return [
            self.copy(self.rest, self.stage),
            self.unpair(self.a, self.c, self.rest),
            self.move(self.rest, self.c),
            self.a.inc,
            self.emit_preserving(self.a),
            self.move(self.count, self.a),
            self.formula_index(),
            self.label('record', [self.prefix(), self.walk()]),
            self.clear(self.a), self.clear(self.c),
            self.while_decnz(self.count, [self.emit_coordinate(), self.clear(self.a)]),
            [self.clear(r) for r in work],
            self.emit_natural(self.top), self.stage.inc,
        ]


def run(out):
    out = Path(out)
    if out.exists():
        raise ValueError('Fresh output directory required')
    return p.opt.compile_candidate(HFieldSharing, out)[1]


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(run(args.out), indent=2))
