#!/usr/bin/env python3
"""Complete the impossible preparation row without allocating a fresh sink.

An admitted primitive preparation enters prep_1 reading the zero separator.
The read-one row is therefore unconstrained by source refinement; give it an
ordinary deterministic row into an already counted state.
"""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path
import run_dispatch
p = run_dispatch.p


class TotalPreparation:
    def generate(self):
        super().generate()
        key = ('1b.reg.prep_1', '1')
        assert key not in self.tm.states
        self.tm.states[key] = p.opt.tm.Transition('1', 'R', '1b.reg.prep_1')


def variant(module, name):
    cls = run_dispatch.variant(module, name)
    return type('Total' + cls.__name__, (TotalPreparation, cls), {})


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--module', required=True)
    parser.add_argument('--class-name', required=True)
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError('Fresh output directory required')
    sys.path.insert(0, str(Path(__file__).resolve().parent / 'architecture'))
    builder, ledger, _ = p.opt.compile_candidate(variant(args.module, args.class_name), args.out)
    (args.out / 'run-dispatch.json').write_text(json.dumps(builder.run_dispatch_certificate,
                                                        sort_keys=True, indent=2) + '\n')
    print(json.dumps(ledger, indent=2))
