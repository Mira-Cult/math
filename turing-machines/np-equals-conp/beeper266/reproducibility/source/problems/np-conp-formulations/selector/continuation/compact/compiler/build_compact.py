"""Complete paid compilation for direct pure-call argument installation."""
from __future__ import annotations

from contextlib import contextmanager
from pathlib import Path
import argparse
import json
import sys

HERE = Path(__file__).resolve().parent
COMPACT = HERE.parent
ARITHMETIC = COMPACT.parent/'arithmetic'
sys.path.insert(0, str(ARITHMETIC))
import integrated
import grammar_rotations
sys.path.insert(0, str(ARITHMETIC/'compiler'))
import mixed_tuples
sys.path.insert(0, str(HERE))
import direct_calls
import return_forward
import direct_half

SOURCE = ARITHMETIC/'source/forced_relative.py'
OPTIONS = dict(lookup=False, pair_half=True,
               options={'affine_assignments': False, 'affine_forward': False})


@contextmanager
def installed(**overrides):
    options = {**OPTIONS, **overrides}
    with mixed_tuples.installed(integrated), direct_calls.installed(integrated), return_forward.installed(integrated), direct_half.installed(integrated):
        with integrated.installed(**options) as instances:
            yield instances


def construct(source=SOURCE, **overrides):
    with installed(**overrides):
        return integrated.build_live.construct(source)


def build(out, source=SOURCE, *, rotations=False, rounds=12, **overrides):
    out = Path(out)
    if rotations:
        builder, *_ = construct(source, **overrides)
        plan = grammar_rotations.search(builder, rounds)
        plan['source_sha256'] = integrated.build_live.baseline.sha(source)
        with installed(**overrides) as instances, grammar_rotations.installed(plan):
            metadata = integrated.build_live.build(out, source)
        integrated.build_live.baseline.dump(out/'rotations.json', plan)
    else:
        with installed(**overrides) as instances:
            metadata = integrated.build_live.build(out, source)
    assert len(instances) == 1
    b = instances[0]
    metadata['format'] = 'np-conp-direct-call-complete-v1'
    metadata['compact_options'] = {**OPTIONS, **overrides, 'rotations': rotations}
    metadata['compact_producers'] = {path.name: integrated.build_live.baseline.sha(path)
        for path in (HERE/'direct_calls.py', HERE/'return_forward.py', HERE/'direct_half.py', HERE/'build_compact.py')}
    for name, data in [('metadata.json', metadata),
                       ('direct-calls.json', b.direct_call_certificate),
                       ('return-forward.json', b.return_forward_certificate),
                       ('direct-half.json', b.direct_half_certificate),
                       ('mixed-tuples.json', b.mixed_tuple_certificate),
                       ('new-arithmetic.json', b.arithmetic_certificate),
                       ('record-pop.json', b.record_pop_certificate)]:
        integrated.build_live.baseline.dump(out/name, data)
    return metadata


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, default=SOURCE)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--rotations', action='store_true')
    parser.add_argument('--rounds', type=int, default=12)
    parser.add_argument('--direct-half', action='store_true')
    args = parser.parse_args()
    options = {**OPTIONS['options'], 'direct_half': args.direct_half}
    result = build(args.out, args.source, rotations=args.rotations, rounds=args.rounds, options=options)
    print(json.dumps({key: result[key] for key in
        ('raw_states', 'states', 'event_states', 'registers', 'profile', 'event_table_sha256')},
        indent=2))
