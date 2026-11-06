"""Complete counted beeper builds with conservative source-liveness allocation.

The inherited selector producer and all its vendor pins stay unchanged.  This
wrapper accepts explicit new sources and records their exact identity; accepting
a source here is a compilation fact, not a proof of its NP=coNP characterization.
"""
from pathlib import Path
from collections import Counter
import argparse
import importlib.util
import json
import sys

HERE = Path(__file__).resolve().parent
SELECTOR = HERE.parent.parent
sys.path.insert(0, str(HERE))
spec = importlib.util.spec_from_file_location('frozen_selector_build', SELECTOR/'build.py')
baseline = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = baseline
spec.loader.exec_module(baseline)
from live_registers import allocated_runtime
from half_pairs import HalfPairBuilder
from contextlib import contextmanager


@contextmanager
def selected_builder(half_pairs):
    original = baseline.ContextualTreeBuilder
    if half_pairs:
        baseline.ContextualTreeBuilder = HalfPairBuilder
    try:
        yield
    finally:
        baseline.ContextualTreeBuilder = original


def construct(source=SELECTOR/'source.py', *, mode='dsatur', allocate=True,
              reuse_returns=True, half_pairs=True):
    with selected_builder(half_pairs):
        if allocate:
            with allocated_runtime(mode, reuse_returns):
                return baseline.construct(Path(source), case='selected', contextual=False)
        return baseline.construct(Path(source), case='selected', contextual=False)


def build(out, source=SELECTOR/'source.py', *, mode='dsatur', allocate=True,
          reuse_returns=True, half_pairs=True):
    source, out = Path(source), Path(out)
    if out.exists():
        raise ValueError('use a fresh output directory')
    b, raw, final, names, mapping, missing, maximum = construct(source, mode=mode,
        allocate=allocate, reuse_returns=reuse_returns, half_pairs=half_pairs)
    out.mkdir(parents=True)
    for filename, machine in [('raw.tm', raw), ('machine.tm', final)]:
        baseline.emit(machine, out/filename)
        if baseline.parse(out/filename).rows != machine.rows:
            raise AssertionError('literal table round trip')
    groups = {}
    for name, q in names.items():
        groups.setdefault(mapping[q], set()).add(baseline.category(name))
    profile = dict(Counter(' + '.join(sorted(values)) for values in groups.values()))
    assert sum(profile.values()) == final.count
    prior = baseline.events.from_legacy(final)
    shifted = baseline.events.ingress(prior, final.beep)
    baseline.events.check_ingress(prior, shifted, final.beep)
    event, event_map = baseline.events.quotient(shifted)
    baseline.events.check_quotient(shifted, event, event_map)
    baseline.events.emit(shifted, out/'ingress-prequotient.tm')
    baseline.events.emit(event, out/'events.tm')
    metadata = dict(format='np-conp-source-liveness-complete-v1',
        allocation=allocate, allocation_mode=mode, reuse_returns=reuse_returns,
        half_pairs=half_pairs, states=final.count,
        rows=len(final.rows), raw_states=raw.count, event_states=event.count,
        event_rows=len(event.rows), registers=len(b.registers),
        source_sha256=baseline.sha(source), table_sha256=baseline.sha(out/'machine.tm'),
        event_table_sha256=baseline.sha(out/'events.tm'),
        raw_table_sha256=baseline.sha(out/'raw.tm'),
        profile=profile, options=b.transfer_options,
        source_changed=baseline.sha(source) != baseline.SOURCE_SHA256,
        blank=0, head=0, start=final.start, B=final.beep,
        alphabet=[0, 1], moves=['L', 'R'], tape_geometry='two-way infinite',
        event_convention='events.tm sixth column marks the applied transition',
        B_event_convention='machine.tm exits from B before applying its row',
        halt_states_excluded=0, max_leaf_path=maximum,
        bootstrap_bank_anchor_after_translation=3824,
        bootstrap_zero_register_capacity=1909, bootstrap_verified_bounds=True,
        tuple_positivity=getattr(b, 'positivity_certificates', None),
        totalization_requests=missing,
        source_entry='main().0', source_entry_raw_state=names['main().0'],
        source_entry_final_state=mapping[names['main().0']],
        register_order=list(b.registers),
        initialization_proof_status='requires separate exact blank-entry replay',
        proof_status='new source-liveness continuation; independent review required',
        producer_sources={name: baseline.sha(HERE/name)
                          for name in ('build_live.py', 'live_registers.py', 'half_pairs.py')},
        inherited_producer={name: baseline.sha(SELECTOR/name)
                            for name in ('build.py', 'applicability.py', 'provenance.json')})
    artifacts = [('grammar.json', baseline.grammar(b)), ('names.json', names),
        ('quotient.json', mapping), ('metadata.json', metadata),
        ('allocation.json', b.frame_pool_certificate),
        ('half-pairs.json', getattr(b, 'half_pair_certificate', [])),
        ('dead-entry-extension.json', b.dead_entry_extension),
        ('selector.json', b.selector_certificate),
        ('refactoring.json', b.closed_sequence_certificate),
        ('fusion.json', b.fused_consuming_certificate),
        ('contextual-tree-certificate.json', b.contextual_tree_certificate),
        ('countdown.json', b.countdown_certificate), ('horner.json', b.horner_certificate),
        ('event-quotient.json', dict(format='np-conp-ingress-event-quotient-v1',
            source_table_sha256=baseline.sha(out/'machine.tm'),
            predecessor_sha256=baseline.sha(out/'ingress-prequotient.tm'),
            result_sha256=baseline.sha(out/'events.tm'), source_B=final.beep,
            time_shift=-1, mapping=event_map)),
        ('event-metadata.json', dict(states=event.count, rows=len(event.rows),
            start=event.start, source_sha256=baseline.sha(source),
            table_sha256=baseline.sha(out/'events.tm'), blank=0, head=0,
            event_rows=[[q, r, *v] for (q, r), v in sorted(event.rows.items()) if v[3]],
            halt_states_excluded=0,
            event_convention='sixth table column; marked transition applied',
            B_exit_parent_states=final.count,
            B_exit_parent_sha256=baseline.sha(out/'machine.tm')))]
    for filename, value in artifacts:
        baseline.dump(out/filename, value)
    return metadata


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, default=SELECTOR/'source.py')
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--mode', choices=('dsatur', 'degree', 'source'), default='dsatur')
    parser.add_argument('--no-allocation', action='store_true')
    parser.add_argument('--protect-returns', action='store_true')
    parser.add_argument('--no-half-pairs', action='store_true')
    args = parser.parse_args()
    result = build(args.out, args.source, mode=args.mode, allocate=not args.no_allocation,
                   reuse_returns=not args.protect_returns, half_pairs=not args.no_half_pairs)
    print(json.dumps({key: result[key] for key in ('states', 'event_states', 'rows',
        'raw_states', 'registers', 'source_sha256', 'event_table_sha256', 'profile')}, indent=2))
