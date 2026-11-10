#!/usr/bin/env python3
"""Paid nine-register experiment: explicit positive/negative traversal phases.

The initial negative path consumes its same alignment coordinate, executes
one negative step, then joins a loop of positive/negative step pairs. The
temporary prefix copy of y borrows env while that cell is still zero.
"""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
import boolean_joins
from TMBuilder import subroutine

p = boolean_joins.p


class PairedPolarity(boolean_joins.ReturnInSign):
    def __init__(self, source):
        p.opt.build.OmegaBuilder.__init__(self, 'def main():\n    while True:\n        emit0()\n', share=False)
        self.reference_source = source
        for name in ('stage', 'rest', 'count', 'top', 'env', 'a', 'b', 'c'):
            setattr(self, name, self.reg('k.' + name))

    @subroutine
    def unsigned_prefix(self):
        return [
            self.take(), self.move(self.b, self.a), self.take(),
            self.while_decnz(self.a, [
                self.if_not_decnz(self.count, [self.move(self.count, self.c), self.finish_true()]),
                self.c.inc,
            ]),
            self.while_decnz(self.c, [self.count.inc, self.a.inc, self.env.inc]),
            self.bit_b_a(), self.move(self.a, self.env), self.bind_a(),
        ]

    @subroutine
    def h_step(self):
        return [
            self.take(), self.unpair(self.c, self.scratch, self.b),
            self.label('branch', [
                self.if_decnz(self.a, [self.clear(self.c), self.move(self.c, self.scratch), 'break_branch']),
                self.clear(self.scratch),
            ]),
            self.move(self.top, self.c), self.bind_a(),
        ]

    @subroutine
    def atom_bit(self):
        return [
            self.unpair(self.c, self.scratch, self.b),
            self.move(self.a, self.c), self.move(self.top, self.scratch), self.lookup_a(),
            self.move(self.c, self.a), self.move(self.a, self.top), self.move(self.top, self.c),
            self.lookup_a(), self.move(self.b, self.top), self.bit_b_a(),
        ]

    @subroutine
    def signed_step(self, negative):
        return [
            self.divbase(self.b, self.c, self.top, 2),
            self.label('step', [
                self.if_decnz(self.c, [self.h_step(), 'break_step']),
                self.atom_bit(), [] if negative else self.toggle(self.b),
                self.move(self.top, self.b), 'break_record',
            ]),
        ]

    @subroutine
    def main(self):
        work = (self.rest, self.env, self.a, self.b, self.c, self.scratch)
        return [
            self.copy(self.rest, self.stage), self.unpair(self.a, self.c, self.rest),
            self.move(self.rest, self.c), self.a.inc, self.emit_preserving(self.a),
            self.move(self.count, self.a), self.formula_index(),
            self.label('record', [
                self.unsigned_prefix(),
                self.if_not_decnz(self.b, [self.take(), self.clear(self.a), self.signed_step(True)]),
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
    print(json.dumps(p.opt.compile_candidate(PairedPolarity, args.out)[1], indent=2))
