#!/usr/bin/env python3
"""Count consecutive PC zeros when redispatching, resetting at each one.

The bound is recomputed from all complete grammar leaf paths, including the
110 root prefix.  This changes physical rows, not the ordered primitive graph.
"""
from __future__ import annotations
import argparse
import importlib
import json
import sys
from pathlib import Path
import spent_rank
p = spent_rank.p


def path_run_bound(builder):
    root = builder.find_seq('main().0')
    paths = []
    def walk(node, prefix):
        if not isinstance(node, int):
            paths.append(prefix)
            return
        children = builder.sequences[node].seq
        assert len(children) == 2
        for bit, child in enumerate(children):
            walk(child, prefix + str(bit))
    walk(root, '110')
    longest = max(max(map(len, word.split('1'))) for word in paths)
    return max(1, longest), len(paths)


class RunDispatch:
    def generate(self):
        super().generate()
        longest, leaves = path_run_bound(self)
        self.run_dispatch_certificate = {'max_zero_run': longest, 'leaf_paths': leaves,
            'prefix': '110', 'threshold': longest + 1}
        for key in list(self.tm.states):
            if key[0].startswith('4.dispatch.') and key[0] != '4.dispatch.scan':
                del self.tm.states[key]
        tm = p.opt.tm
        largest = f'4.dispatch.{longest}'
        for count in range(longest + 1):
            name = f'4.dispatch.{count}'
            target = f'4.dispatch.{count-1}' if count else '4.dispatch.scan'
            self.tm.states[name, '0'] = tm.Transition('0', 'L', target)
            self.tm.states[name, '1'] = tm.Transition('1', 'L', largest)
        self.tm.states['6.continue.0', '1'] = tm.Transition('1', 'L', largest)


def variant(module, name):
    cls = getattr(importlib.import_module(module), name)
    return type('Run' + name, (RunDispatch, cls), {})


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
