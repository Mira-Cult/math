"""Fresh admitted-row completion; discovery is separate from fixed replay.

The parent is the complete direct-branches producer. No numerical holes or
completion partition from an earlier table are inherited. Every raw preimage
of an excluded quotient row is checked against named primitive-domain facts.
"""
from collections import Counter, defaultdict
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import random
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
COMPACT = ROOT.parent
sys.path.insert(0, str(ROOT/'control'))
import build as control


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


completion = module('binary_phase_completion', COMPACT/'tape_local/completion/complete.py')
reader = module('binary_phase_literal_reader', COMPACT/'tape_local/review/binary_kernel/check_endpoint.py')
categories = module('binary_phase_categories', COMPACT/'native/cost_check.py')
baseline = control.build_coalesced.baseline
SOURCE = ROOT/'control/source_direct_branches.py'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, sort_keys=True, indent=2)+'\n')


def domain(parent):
    parent = Path(parent)
    parent_metadata = reader.read(parent/'metadata.json')
    assert sha(SOURCE) == parent_metadata['source_sha256'], 'source differs from complete parent'
    names = reader.read(parent/'names.json')
    mapping = reader.read(parent/'quotient.json')
    requests = reader.read(parent/'selector.json')['new_totalized_rows']
    requested = {(names[name], int(bit)) for name, bit in requests}
    requested.update((names['silent.sink'], bit) for bit in (0, 1))
    preimages = defaultdict(list)
    for old in names.values():
        preimages[reader.mapped(mapping, old)].append(old)
    holes = {(q, bit) for q, olds in preimages.items() for bit in (0, 1)
             if all((old, bit) in requested for old in olds)}
    header, rows = reader.table(parent/'machine.tm')
    sink = reader.mapped(mapping, names['silent.sink'])
    assert all(rows[key][2] == sink for key in holes)
    certificate = dict(format='np-conp-binary-phase-fresh-domain-v1',
        source_sha256=sha(SOURCE), control_sha256=sha(parent/'machine.tm'),
        convention='B', source_request_file_sha256=sha(parent/'selector.json'),
        names_sha256=sha(parent/'names.json'), raw_quotient_sha256=sha(parent/'quotient.json'),
        requests=requests, holes=[list(key) for key in sorted(holes)], sink=sink,
        preimages={str(q): preimages[q] for q, _ in sorted(holes)},
        premise='The new source and lowering, fresh storage certificates, and unchanged named unary/HALF/selector segment contracts exclude these named reads. All raw preimages are checked; membership in totalization metadata alone is not a proof.')
    return rows, holes, certificate


def discover(parent, path, rounds):
    rows, holes, certificate = domain(parent)
    pairs = completion.compatible_pairs(rows, holes)
    best = None
    trials = []
    for seed in range(rounds):
        order = list(pairs)
        if seed:
            random.Random(seed).shuffle(order)
        partition = completion.Partition(rows, holes)
        for a, b in order:
            # Even a state with both rows excluded is not the distinguished
            # B state. Protect that state color through recursive target
            # merges as well as through the initially proposed pair.
            saved = (partition.parent.copy(), [x.copy() for x in partition.data],
                     partition.count)
            if partition.merge(a, b) and any(
                    q != 1 and partition.root(q) == partition.root(1)
                    for q in range(len(rows)//2)):
                partition.parent, partition.data, partition.count = saved
        mapping = partition.mapping()
        completion.validate(rows, holes, mapping)
        assert mapping[0] == 0 and mapping[1] == 1
        assert [q for q, v in enumerate(mapping) if v == 1] == [1]
        trials.append(dict(seed=seed, states=partition.count))
        if best is None or partition.count < best[0]:
            best = partition.count, mapping, seed
    plan = dict(format='np-conp-binary-phase-completion-plan-v1',
        source_sha256=sha(SOURCE), control_sha256=certificate['control_sha256'],
        convention='B', holes=certificate['holes'], mapping=best[1], states=best[0],
        selected_seed=best[2], trials=trials, compatible_pairs=len(pairs),
        scope='bounded deterministic discovery; no optimality claim; replay does not run this search')
    dump(path, plan)
    return {key: plan[key] for key in ('states', 'selected_seed', 'compatible_pairs')}


def build(parent, out, plan_path):
    parent, out, plan_path = Path(parent), Path(out), Path(plan_path)
    if out.exists():
        raise ValueError('fresh output directory required')
    rows, holes, certificate = domain(parent)
    plan = reader.read(plan_path)
    assert plan['format'] == 'np-conp-binary-phase-completion-plan-v1'
    assert plan['source_sha256'] == sha(SOURCE)
    assert plan['control_sha256'] == certificate['control_sha256']
    assert plan['holes'] == certificate['holes'] and plan['convention'] == 'B'
    mapping = plan['mapping']
    final = completion.validate(rows, holes, mapping)
    assert mapping[0] == 0 and mapping[1] == 1
    assert [q for q, value in enumerate(mapping) if value == 1] == [1]
    representative = {}
    for q, target in enumerate(mapping):
        representative.setdefault(target, q)
    completed = dict(rows)
    for q, bit in holes:
        w, d, target, event = final[mapping[q], bit]
        completed[q, bit] = w, d, representative[target], event
    assert all(completed[key] == rows[key] for key in rows if key not in holes)
    out.mkdir(parents=True)
    completion.emit(completed, out/'raw.tm', beep=1)
    completion.emit(final, out/'machine.tm', beep=1)
    raw, companion = baseline.parse(out/'raw.tm'), baseline.parse(out/'machine.tm')
    baseline.check_quotient(raw, companion, dict(enumerate(mapping)))
    ingress = baseline.events.ingress(baseline.events.from_legacy(companion), 1)
    baseline.events.check_ingress(baseline.events.from_legacy(companion), ingress, 1)
    events, event_map = baseline.events.quotient(ingress)
    baseline.events.check_quotient(ingress, events, event_map)
    baseline.events.emit(ingress, out/'ingress-prequotient.tm')
    baseline.events.emit(events, out/'events.tm')
    parent_metadata = reader.read(parent/'metadata.json')
    metadata = dict(format='np-conp-binary-phase-selected-v1',
        source_sha256=sha(SOURCE), source_changed=True,
        source_change='same normalized reference and candidate predicates; ordinal reuse and direct parity branches in acceptance; supplied source identifies either original or direct marker/payload parser',
        raw_states=raw.count, states=companion.count, event_states=events.count,
        raw_rows=len(raw.rows), rows=len(companion.rows), event_rows=len(events.rows),
        raw_table_sha256=sha(out/'raw.tm'), table_sha256=sha(out/'machine.tm'),
        event_table_sha256=sha(out/'events.tm'), parent_table_sha256=certificate['control_sha256'],
        initial=dict(start=0, head=0, blank=0, tape='two-way infinite', alphabet=[0, 1], moves=['L', 'R']),
        B=1, halt_states_excluded=0, registers=parent_metadata['registers'],
        source_entry_final_state=mapping[parent_metadata['source_entry_final_state']],
        marked_rows=[[q, bit, *value] for (q, bit), value in sorted(events.rows.items()) if value[3]],
        plan_sha256=sha(plan_path), generator_sha256=sha(Path(__file__)),
        source_event_contract='finite marks iff NP=coNP; infinite physical run in both cases',
        event_trace_relation='marked ingress one physical transition before B exit; new source internal histories differ from387',
        fixed_plan=True, optimization_search=False)
    dump(out/'metadata.json', metadata)
    dump(out/'domain.json', certificate)
    dump(out/'quotient.json', dict(enumerate(mapping)))
    dump(out/'completion.json', dict(format='np-conp-unreachable-row-completion-v1',
        source_sha256=sha(parent/'machine.tm'), target_sha256=sha(out/'raw.tm'),
        retained_rows=len(rows)-len(holes),
        changes=[dict(state=q, read=bit, before=list(rows[q, bit]), after=list(completed[q, bit])) for q, bit in sorted(holes)]))
    dump(out/'event-quotient.json', dict(format='np-conp-ingress-event-quotient-v1',
        source_table_sha256=sha(out/'machine.tm'), predecessor_sha256=sha(out/'ingress-prequotient.tm'),
        result_sha256=sha(out/'events.tm'), source_B=1, time_shift=-1, mapping=event_map))
    first = reader.read(parent/'quotient.json')
    names = reader.read(parent/'names.json')
    classes = defaultdict(set)
    for name, q in names.items():
        target = reader.mapped(event_map, mapping[reader.mapped(first, q)])
        classes[target].add(categories.category(name))
    partition = dict(sorted(Counter(' + '.join(sorted(v)) for v in classes.values()).items()))
    assert sum(partition.values()) == events.count
    dump(out/'physical-ledger.json', dict(format='np-conp-binary-phase-disjoint-cost-v1',
        disjoint_event_partition=partition, states=events.count, rows=len(events.rows),
        source_sha256=sha(SOURCE), event_table_sha256=sha(out/'events.tm'),
        classes={str(q): sorted(v) for q, v in sorted(classes.items())},
        scope='one count per actual quotient state, with all construction origins retained; no global lower bound'))
    return {key: metadata[key] for key in ('raw_states', 'states', 'event_states', 'event_table_sha256', 'marked_rows')}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--parent', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--plan', type=Path)
    parser.add_argument('--discover', action='store_true')
    parser.add_argument('--rounds', type=int, default=64)
    parser.add_argument('--source', type=Path, default=SOURCE,
                        help='exact source used by the supplied complete parent')
    args = parser.parse_args()
    SOURCE = args.source.resolve()
    if args.discover:
        assert args.plan is None
        result = discover(args.parent, args.out, args.rounds)
    else:
        assert args.plan is not None
        result = build(args.parent, args.out, args.plan)
    print(json.dumps(result, sort_keys=True, indent=2))
