"""Independent source identity and actual three-transfer swap review.

The frozen predecessor's independent tuple-path/closure checker is reused,
not a producer graph extractor or the new swap checker's own implementation.
"""
import argparse
import ast
from copy import deepcopy
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parents[1]
COMPACT = PACKAGE.parent
PREVIOUS = COMPACT / 'transfer328/review/source/check_closed_regions.py'
spec = importlib.util.spec_from_file_location('previous_independent_tuple_paths', PREVIOUS)
previous = importlib.util.module_from_spec(spec)
spec.loader.exec_module(previous)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def locate_all(rows, pattern):
    matches = []
    for candidate in rows:
        mapped, pending, valid = {0: candidate}, [0], True
        while pending and valid:
            node = pending.pop()
            if node == len(pattern):
                continue
            expected, actual = pattern[node], rows[mapped[node]]
            if actual[0] != expected[0] or len(actual) != len(expected):
                valid = False
                break
            for label, target in zip(expected[1:], actual[1:]):
                if label in mapped:
                    valid = valid and mapped[label] == target
                else:
                    mapped[label] = target
                    pending.append(label)
        if not valid or len(mapped) != len(pattern) + 1 or len(set(mapped.values())) != len(mapped):
            continue
        inside = {mapped[k] for k in range(len(pattern))}
        incoming = [(src, dst) for src, row in rows.items() if src not in inside
                    for dst in row[1:] if dst in inside]
        outgoing = [(src, dst) for src in inside for dst in rows[src][1:] if dst not in inside]
        assert incoming and {dst for _, dst in incoming} == {candidate}, 'nonlocal swap entry'
        assert len(outgoing) == 1 and outgoing[0][1] == mapped[len(pattern)], 'nonlocal swap exit'
        matches.append((mapped, incoming, outgoing))
    return sorted(matches, key=lambda x: x[0][0])


def edge_work_image(graph, invariant, source, destination, work):
    """Branch-specific mask after one retained operation and finite jumps."""
    before = invariant['states_at_occurrences'][graph.indices[source]]
    if before is None:
        return 0
    work_slot = graph.g['registers'].index(work)
    operation, *targets = graph.rows[source]
    if operation == 'beep':
        return int(before[work_slot]) if targets[0] == destination else 0
    name, action = operation[2:].rsplit('.', 1)
    half = name.startswith('$native-half:')
    if half:
        name = name[len('$native-half:'):]
    operand_mask = int(before[graph.g['registers'].index(name)])
    result = 0
    for value, mask in ((0, 1), (1, 2), (2, 4), (3, 4), (4, 4), (5, 4)):
        if not operand_mask & mask:
            continue
        arm = int(value % 2 == 0) if half else int(action == 'decnz' and value == 0)
        if targets[arm] != destination:
            continue
        if name != work:
            result |= int(before[work_slot])
        else:
            after = value // 2 if half else value + 1 if action == 'inc' else max(0, value - 1)
            result |= 1 if after == 0 else 2 if after == 1 else 4
    return result


def region_premises(graph, invariant, sharing, roles, pattern, turn):
    assert len(set(roles)) == len({sharing[x] for x in roles}) == 3, 'swap operands alias'
    matches = locate_all(graph.rows, pattern)
    assert len(matches) == 2, 'both actual swap regions must match'
    for _, incoming, _ in matches:
        for src, dst in incoming:
            row = graph.rows[src]
            assert row[0] == '3.$native-half:' + turn + '.decnz'
            assert row[1] == dst and row[2] != dst, 'swap must be entered only on the positive turn arm'
        images = [edge_work_image(graph, invariant, src, dst, roles[2]) for src, dst in incoming]
        assert any(images) and all(image in (0, 1) for image in images), \
            'swap work not exactly zero on every admitted outside entry'
    return matches


def run(parent, source):
    old = COMPACT / 'transfer328/control/attempt_reset/source.py'
    assert source.read_bytes() == old.read_bytes()
    assert sha(source) == '4f1f6f317eb196b8d09a67439893622a759c43ef4e02e30adae4e04b0eb39515'
    read = lambda name: json.loads((parent / name).read_text())
    grammar = read('pre-coalescence-grammar.json')
    graph = previous.TupleGraph(grammar)
    invariant = read('coalescence-invariant.json')
    allocation = read('allocation.json')['mapping']
    sharing = read('bank-coalescence.json')['mapping']
    summary = previous.check_closure(graph, invariant, sharing)
    certificates = read('three-move-swap.json')
    swaps = [node for node in ast.walk(ast.parse(source.read_text()))
             if isinstance(node, ast.Assign) and ast.unparse(node) == 'left, right = (right, left)']
    assert len(swaps) == len(certificates) == 2
    assert sorted((node.lineno, ast.dump(node, include_attributes=False)) for node in swaps) == sorted(
        (certificate['line'], certificate['exact_ast']) for certificate in certificates)
    assert all(certificate['function'] == 'main' for certificate in certificates)
    roles = []
    for certificate in certificates:
        assert [certificate[x] for x in ('left', 'right', 'work')] == ['main.left', 'main.right', '$micro.q']
        roles.append(tuple(allocation.get(certificate[x], certificate[x]) for x in ('left', 'right', 'work')))
    assert roles[0] == roles[1]
    L, R, Q = roles[0]
    op = lambda carrier, action: '3.' + carrier + '.' + action
    pattern = [(op(L, 'decnz'), 1, 2), (op(Q, 'inc'), 0),
               (op(R, 'decnz'), 3, 4), (op(L, 'inc'), 2),
               (op(Q, 'decnz'), 5, 6), (op(R, 'inc'), 4)]
    turn = allocation['main.state']
    matches = region_premises(graph, invariant, sharing, roles[0], pattern, turn)
    Qslot = grammar['registers'].index(Q)
    fixtures = list(product((0, 1, 2, 3, 7, 31, 127, 255), repeat=2)) + [(1024, 2047), (4096, 0), (0, 4096)]
    regions, total = [], 0
    for mapping, incoming, outgoing in matches:
        entry_index = graph.indices[mapping[0]]
        steps_sum = 0
        for left, right in fixtures:
            before = {name: 100 + i for i, name in enumerate(grammar['registers'])}
            before.update({L: left, R: right, Q: 0})
            middle1, steps1 = previous.execute(graph.rows, mapping[0], mapping[2], before)
            expected1 = dict(before, **{L: 0, R: right, Q: left})
            assert middle1 == expected1
            middle2, steps2 = previous.execute(graph.rows, mapping[2], mapping[4], middle1)
            expected2 = dict(before, **{L: right, R: 0, Q: left})
            assert middle2 == expected2
            after, steps3 = previous.execute(graph.rows, mapping[4], mapping[6], middle2)
            expected = dict(before, **{L: right, R: left, Q: 0})
            assert after == expected
            assert steps1 + steps2 + steps3 == 4 * left + 2 * right + 3 > 0
            steps_sum += steps1 + steps2 + steps3
        total += steps_sum
        regions.append(dict(entry=''.join(map(str, mapping[0])), rows=6,
            sole_ingress_targets=1, outside_ingress_edges=len(incoming), outside_exit_edges=len(outgoing),
            work_outside_entry_images=[edge_work_image(graph, invariant, src, dst, Q) for src, dst in incoming],
            outside_entry_operations=[graph.rows[src][0] for src, _ in incoming],
            joined_loop_header_work_mask=invariant['states_at_occurrences'][entry_index][Qslot],
            logical_carriers=[L, R, Q], physical_carriers=[sharing[x] for x in (L, R, Q)],
            fixtures=len(fixtures), primitive_steps=steps_sum))

    damaged = []
    mapping = matches[0][0]
    broken = deepcopy(graph)
    broken.rows[mapping[5]] = (op(L, 'inc'), mapping[4])
    bad_masks = deepcopy(invariant)
    index = graph.indices[matches[0][1][0][0]]
    mask = list(bad_masks['states_at_occurrences'][index]); mask[Qslot] = '3'
    bad_masks['states_at_occurrences'][index] = ''.join(mask)
    aliased = dict(sharing); aliased[Q] = aliased[L]
    reversed_turn = deepcopy(graph)
    outside = matches[0][1][0][0]
    row = reversed_turn.rows[outside]
    reversed_turn.rows[outside] = (row[0], row[2], row[1])
    for label, changed_graph, changed_masks, changed_classes in [
        ('final restoration increment targets the wrong half', broken, invariant, sharing),
        ('outside incoming work mask permits nonzero scratch', graph, bad_masks, sharing),
        ('work carrier aliases the old left half', graph, invariant, aliased),
        ('zero turn arm enters the orientation swap', reversed_turn, invariant, sharing),
    ]:
        try:
            region_premises(changed_graph, changed_masks, changed_classes, roles[0], pattern, turn)
        except AssertionError:
            damaged.append(label)
        else:
            raise AssertionError('damaged case accepted: ' + label)
    # Demonstrate why the exact-zero premise is necessary, independently of
    # abstract propagation: with Q initially one, the result is not a swap.
    before = {name: 0 for name in grammar['registers']}
    before.update({L: 2, R: 3, Q: 1})
    after, _ = previous.execute(graph.rows, mapping[0], mapping[6], before)
    assert (after[L], after[R], after[Q]) == (3, 3, 0)
    return dict(schema='npconp-phase-swap-independent-source-regions-v1',
        source_sha256=sha(source), source_identical_to_291_producer=True,
        predecessor_producer='81147084e3d81219073ba6b8f0e6a3e3af8cf116',
        source_swap_AST_sites=len(swaps), **summary, regions=regions,
        fixtures=len(fixtures) * len(matches), primitive_steps=total,
        necessary_zero_premise_counterexample=dict(before=[2, 3, 1], actual_after=[3, 3, 0], required_after=[3, 2, 0]),
        damaged_cases_rejected=damaged,
        inputs={name: sha(parent / name) for name in ('pre-coalescence-grammar.json', 'allocation.json',
            'bank-coalescence.json', 'coalescence-invariant.json', 'three-move-swap.json')},
        lowerer_sha256=sha(PACKAGE / 'region.py'), independent_tuple_checker_sha256=sha(PREVIOUS),
        scope='Exact source identity, both actual swap-region recurrences and boundaries, all supplied abstract closure and ordinary-operation zero peers, exact entry-zero work and distinct physical operands; prepared logical fixtures, not literal blank execution')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--parent', type=Path, default=PACKAGE / 'machines/parent290')
    parser.add_argument('--source', type=Path, default=PACKAGE / 'source.py')
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.parent.resolve(), args.source.resolve())
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps(result, sort_keys=True, indent=2))
