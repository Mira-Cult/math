"""Complete binary blank-start build with paid native half/parity control."""
from contextlib import contextmanager
from pathlib import Path
import argparse
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import build_compact
sys.path.insert(0, str(HERE))
import half_engine
import abstract_half
import check_contextual
from lower_half import NativeHalfMixin
import contextual_tree
import check_contextual_tree
import live_registers
sys.path.insert(0, str(HERE.parents[1]))
import weak_grammar

DEFAULT_SOURCE = HERE.parents[1]/'source/certificate_popfirst_power.py'


@contextmanager
def installed():
    with build_compact.installed() as instances:
        old = build_compact.integrated.build_live.HalfPairBuilder
        analyze, check, apply = contextual_tree.analyze, check_contextual_tree.check, contextual_tree.apply
        pool = live_registers.pool_frames
        class NativeBuilder(NativeHalfMixin, old):
            pass
        def native_apply(builder):
            certificate = apply(builder)
            certificate['schema'] = 'np-conp-native-half-contextual-v1'
            certificate['native_half_domain'] = 'zero/one/many with odd/even quotient images; checker in native/check_contextual.py'
            return certificate
        def native_pool(builder, **options):
            # The original source-CFG allocator changes names only. Temporarily
            # expose each native operand's actual register name to that pass;
            # restore its operation tag before any semantic grammar analysis.
            occurrences = []
            for sequence in builder.sequences:
                children = list(sequence.seq)
                for index, child in enumerate(children):
                    register = half_engine.operand(child) if isinstance(child, str) else None
                    if register is not None:
                        occurrences.append((sequence, index, register))
                        children[index] = '3.'+register+'.decnz'
                sequence.seq = tuple(children)
            result = pool(builder, **options)
            for sequence, index, register in occurrences:
                children = list(sequence.seq)
                children[index] = half_engine.operation(builder.logical_to_physical[register])
                sequence.seq = tuple(children)
            builder.native_half_registers = {
                builder.registers[builder.logical_to_physical[str(register)]]
                for register in builder.native_half_registers}
            half_engine.permute(builder)
            return result
        build_compact.integrated.build_live.HalfPairBuilder = NativeBuilder
        contextual_tree.analyze = abstract_half.analyze
        check_contextual_tree.check = check_contextual.check
        contextual_tree.apply = native_apply
        live_registers.pool_frames = native_pool
        try:
            yield instances
        finally:
            build_compact.integrated.build_live.HalfPairBuilder = old
            contextual_tree.analyze, check_contextual_tree.check, contextual_tree.apply = analyze, check, apply
            live_registers.pool_frames = pool


def construct(source=DEFAULT_SOURCE):
    with installed():
        return build_compact.integrated.build_live.construct(source)


def build(out, source=DEFAULT_SOURCE, *, rotations=False, weak=False, broad=False):
    baseline = build_compact.integrated.build_live.baseline
    out = Path(out)
    if weak:
        builder, *_ = construct(source)
        plan = weak_grammar.search(builder, broad=broad)
        plan['source_sha256'] = baseline.sha(source)
        with installed() as instances, weak_grammar.installed(plan):
            metadata = build_compact.integrated.build_live.build(out, source)
        baseline.dump(out/'weak-grammar-plan.json', plan)
        baseline.dump(out/'pre-control-grammar.json', instances[0].weak_input_grammar)
        metadata['contextual_tree_certificate_scope'] = 'pre-control-grammar.json; native abstract transfers; weak-grammar-plan.json links final grammar'
    elif rotations:
        builder, *_ = construct(source)
        plan = build_compact.grammar_rotations.search(builder)
        plan['source_sha256'] = baseline.sha(source)
        with installed() as instances, build_compact.grammar_rotations.installed(plan):
            metadata = build_compact.integrated.build_live.build(out, source)
        baseline.dump(out/'rotations.json', plan)
    else:
        with installed() as instances:
            metadata = build_compact.integrated.build_live.build(out, source)
    assert len(instances) == 1
    builder = instances[0]
    metadata['format'] = 'np-conp-native-half-complete-v1'
    metadata['native_producers'] = {path.name: baseline.sha(path) for path in HERE.glob('*.py')}
    metadata['native_runtime'] = builder.native_half_runtime_certificate
    metadata['native_bank_permutation'] = builder.native_bank_permutation
    for name, value in [('metadata.json', metadata),
                        ('native-half.json', builder.native_half_certificate),
                        ('native-runtime.json', builder.native_half_runtime_certificate),
                        ('native-bank-permutation.json', builder.native_bank_permutation),
                        ('direct-calls.json', builder.direct_call_certificate),
                        ('return-forward.json', builder.return_forward_certificate)]:
        baseline.dump(out/name, value)
    return metadata


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, default=DEFAULT_SOURCE)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--rotations', action='store_true')
    parser.add_argument('--weak', action='store_true')
    parser.add_argument('--broad', action='store_true')
    args = parser.parse_args()
    result = build(args.out, args.source, rotations=args.rotations, weak=args.weak, broad=args.broad)
    print(json.dumps({key: result[key] for key in ('event_states', 'states', 'raw_states',
        'registers', 'profile', 'event_table_sha256')}, indent=2))
