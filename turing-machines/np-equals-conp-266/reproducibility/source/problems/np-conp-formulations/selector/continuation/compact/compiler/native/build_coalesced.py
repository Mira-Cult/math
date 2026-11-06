"""Complete paid zero-partner register coalescence; source unchanged."""
from contextlib import contextmanager
from pathlib import Path
import argparse
import json

import build_native
from zero_coalescence import ZeroCoalescenceMixin

baseline = build_native.build_compact.integrated.build_live.baseline
build_live = build_native.build_compact.integrated.build_live
weak_grammar = build_native.weak_grammar
SOURCE = build_native.DEFAULT_SOURCE


@contextmanager
def installed(*, native=True, groups=None):
    base = build_native if native else build_native.build_compact
    with base.installed() as instances:
        original = build_live.HalfPairBuilder
        class Coalesced(ZeroCoalescenceMixin, original):
            coalescence_groups = groups
        build_live.HalfPairBuilder = Coalesced
        try:
            yield instances
        finally:
            build_live.HalfPairBuilder = original


def construct(source=SOURCE, *, native=True, groups=None):
    with installed(native=native, groups=groups):
        return build_live.construct(source)


def build(out, source=SOURCE, *, native=True, weak=True, groups=None):
    out = Path(out)
    if weak:
        base = build_native if native else build_native.build_compact
        builder, *_ = base.construct(source)
        plan = weak_grammar.search(builder)
        plan['source_sha256'] = baseline.sha(source)
        with installed(native=native, groups=groups) as instances, weak_grammar.installed(plan):
            metadata = build_live.build(out, source)
        baseline.dump(out/'weak-grammar-plan.json', plan)
        baseline.dump(out/'pre-control-grammar.json', instances[0].weak_input_grammar)
    else:
        with installed(native=native, groups=groups) as instances:
            metadata = build_live.build(out, source)
    assert len(instances) == 1
    builder = instances[0]
    metadata['format'] = 'np-conp-zero-partner-coalescence-complete-v1'
    metadata['native_half'] = native
    metadata['coalescence_producers'] = {path.name: baseline.sha(path) for path in Path(__file__).parent.glob('*.py')}
    metadata['contextual_tree_certificate_scope'] = ('pre-control-grammar.json' if weak else 'pre-projection-grammar.json')+' with original carrier'
    metadata['finite_control_certificate_scope'] = 'pre-control-grammar.json to pre-projection-grammar.json' if weak else 'identity'
    metadata['projection_certificate_scope'] = 'pre-projection-grammar.json to pre-coalescence-grammar.json'
    metadata['allocation_certificate_scope'] = 'original carrier; coalescence uses ghost logical coordinates and a class-sum relation'
    artifacts = [('metadata.json', metadata),
        ('pre-projection-grammar.json', builder.pre_projection_grammar),
        ('bank-projection.json', builder.bank_projection_certificate),
        ('pre-coalescence-grammar.json', builder.pre_coalescence_grammar),
        ('coalescence-invariant.json', builder.coalescence_invariant),
        ('bank-coalescence.json', builder.bank_coalescence_certificate),
        ('direct-calls.json', builder.direct_call_certificate),
        ('return-forward.json', builder.return_forward_certificate)]
    if native:
        metadata['native_runtime'] = builder.native_half_runtime_certificate
        artifacts += [('native-half.json', builder.native_half_certificate),
                      ('native-runtime.json', builder.native_half_runtime_certificate),
                      ('native-bank-permutation.json', builder.native_bank_permutation)]
    for name, value in artifacts:
        baseline.dump(out/name, value)
    return metadata


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, default=SOURCE)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--ordinary', action='store_true')
    parser.add_argument('--groups', type=Path)
    args = parser.parse_args()
    groups = json.loads(args.groups.read_text()) if args.groups else None
    result = build(args.out, args.source, native=not args.ordinary, groups=groups)
    print(json.dumps({key: result[key] for key in ('event_states', 'states', 'raw_states',
        'registers', 'profile', 'event_table_sha256')}, indent=2))
