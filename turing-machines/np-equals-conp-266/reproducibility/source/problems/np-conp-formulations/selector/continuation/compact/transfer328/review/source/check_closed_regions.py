"""Independent tuple-path extraction and closed clock/seed review.

No producer graph extractor, abstract analyzer, region checker or interpreter
is imported. Inputs are the actual frozen JSON grammars and certificates.
"""
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class TupleGraph:
    def __init__(self, grammar):
        self.g = grammar
        self.occurrences = []
        def visit(node, prefix):
            for bit, child in enumerate(grammar['nodes'][node]):
                path = prefix + (bit,)
                if 'node' in child:
                    assert child['node'] < node
                    visit(child['node'], path)
                else:
                    self.occurrences.append((path, child['op']))
        visit(grammar['root'], (1, 1, 0))
        self.indices = {path: k for k, (path, _) in enumerate(self.occurrences)}
        assert len(self.indices) == len(self.occurrences)
        self.rows = {}
        for path, operation in self.occurrences:
            if operation.startswith('_'):
                continue
            targets = [self.retained(self.jump(path, False, 0))]
            if operation.endswith('.decnz'):
                targets.append(self.retained(self.jump(path, False, 1)))
            self.rows[path] = (operation, *targets)

    @staticmethod
    def jump(bits, continuing, count):
        wanted = int(continuing)
        for position in range(len(bits) - 1, -1 if continuing else 1, -1):
            if bits[position] != wanted:
                continue
            if count:
                count -= 1
            else:
                return bits[:position] + (1,)
        raise AssertionError(('escaped root', bits, continuing, count))

    def resolve(self, path):
        path = list(path)
        if path[:3] == [1, 1, 1]:
            path = [1, 1, 0]
        assert path[:3] == [1, 1, 0]
        node, position = self.g['root'], 3
        while True:
            if position == len(path):
                path.append(0)
            child = self.g['nodes'][node][path[position]]
            position += 1
            if 'op' in child:
                assert position == len(path)
                return tuple(path), child['op']
            node = child['node']

    def retained(self, path):
        seen = set()
        while True:
            path, operation = self.resolve(path)
            assert path not in seen, 'administrative-only cycle'
            seen.add(path)
            if not operation.startswith('_'):
                return path
            kind, count = operation[1:].split('.')
            assert kind in ('break', 'continue')
            path = self.jump(path, kind == 'continue', int(count))


def check_closure(graph, certificate, sharing):
    assert certificate['input_grammar'] == graph.g
    states = certificate['states_at_occurrences']
    registers = graph.g['registers']
    assert len(states) == len(graph.occurrences)
    for state in states:
        assert state is None or len(state) == len(registers) and set(state) <= set('1234567')
    initial, _ = graph.resolve((1, 1, 0))
    assert all(int(mask) & 1 for mask in states[graph.indices[initial]])
    edges = operations = 0
    for index, (path, op) in enumerate(graph.occurrences):
        state = states[index]
        if state is None:
            continue
        masks = tuple(map(int, state))
        successors = []
        if op.startswith('_'):
            kind, count = op[1:].split('.')
            successors.append((graph.jump(path, kind == 'continue', int(count)), masks))
        elif op == 'beep':
            successors.append((graph.jump(path, False, 0), masks))
        else:
            assert op.startswith('3.')
            name, action = op[2:].rsplit('.', 1)
            half = name.startswith('$native-half:')
            if half:
                name = name[len('$native-half:'):]
            assert action in ('inc', 'decnz')
            slot = registers.index(name)
            for peer, group in sharing.items():
                if peer != name and group == sharing[name]:
                    assert masks[registers.index(peer)] == 1, ('nonzero physical peer', path, name, peer)
            operations += 1
            images = {}
            for value, mask in ((0, 1), (1, 2), (2, 4), (3, 4), (4, 4), (5, 4)):
                if not masks[slot] & mask:
                    continue
                skip = int(value % 2 == 0) if half else int(action == 'decnz' and value == 0)
                new = value // 2 if half else value + 1 if action == 'inc' else max(0, value - 1)
                dest = graph.jump(path, False, skip)
                images[dest] = images.get(dest, 0) | (1 if new == 0 else 2 if new == 1 else 4)
            for dest, mask in images.items():
                image = list(masks)
                image[slot] = mask
                successors.append((dest, image))
        for dest, image in successors:
            resolved, _ = graph.resolve(dest)
            target = states[graph.indices[resolved]]
            assert target is not None and all(x & ~int(y) == 0 for x, y in zip(image, target))
            edges += 1
    return dict(postfixed_edges=edges, reached_operation_ownership_checks=operations,
                retained_occurrences=len(graph.rows), all_occurrences=len(graph.occurrences))


def locate(rows, specification):
    matches = []
    for candidate in rows:
        mapping = {0: candidate}
        pending, valid = [0], True
        while pending and valid:
            label = pending.pop()
            if label == len(specification):
                continue
            expected = specification[label]
            actual = rows[mapping[label]]
            if actual[0] != expected[0] or len(actual) != len(expected):
                valid = False
                break
            for next_label, destination in zip(expected[1:], actual[1:]):
                if next_label in mapping:
                    if mapping[next_label] != destination:
                        valid = False
                else:
                    mapping[next_label] = destination
                    pending.append(next_label)
        if valid and len(mapping) == len(specification) + 1 and len(set(mapping.values())) == len(mapping):
            inside = {mapping[k] for k in range(len(specification))}
            incoming = [(src, dst) for src, row in rows.items() if src not in inside for dst in row[1:] if dst in inside]
            outgoing = [(src, dst) for src in inside for dst in rows[src][1:] if dst not in inside]
            assert incoming and {dst for _, dst in incoming} == {candidate}
            assert len(outgoing) == 1 and outgoing[0][1] == mapping[len(specification)]
            matches.append((mapping, incoming, outgoing))
    assert len(matches) == 1, ('closed region matches', len(matches))
    return matches[0]


def execute(rows, entry, exit, before):
    bank, pc, steps = dict(before), entry, 0
    while pc != exit:
        assert steps < 4000000
        op, *targets = rows[pc]
        name, action = op[2:].rsplit('.', 1)
        if action == 'inc':
            bank[name] += 1
            pc = targets[0]
        else:
            assert action == 'decnz'
            positive = bank[name] > 0
            bank[name] -= int(positive)
            pc = targets[0 if positive else 1]
        steps += 1
    return bank, steps


def run(parent):
    read = lambda name: json.loads((parent / name).read_text())
    grammar = read('pre-coalescence-grammar.json')
    graph = TupleGraph(grammar)
    allocation = read('allocation.json')['mapping']
    sharing = read('bank-coalescence.json')['mapping']
    invariant = read('coalescence-invariant.json')
    summary = check_closure(graph, invariant, sharing)
    clock, = read('direct-clock.json')
    seed, = read('certificate-seed.json')
    actual_name = lambda name: allocation.get(name, name)
    F, N, K, B, Q, C = [actual_name(clock[key]) for key in
        ('output', 'length_master', 'exponent_master', 'exponent_work', 'product_work', 'copy_scratch')]
    assert len({F, N, K, B, Q, C}) == len({sharing[x] for x in (F, N, K, B, Q, C)}) == 6
    op = lambda name, action: '3.' + name + '.' + action
    clock_spec = [(op(F, 'decnz'), 0, 1), (op(F, 'inc'), 2),
        (op(K, 'decnz'), 3, 13), (op(B, 'inc'), 4),
        (op(F, 'decnz'), 5, 11), (op(N, 'decnz'), 6, 8),
        (op(Q, 'inc'), 7), (op(C, 'inc'), 5),
        (op(C, 'decnz'), 9, 10), (op(N, 'inc'), 8),
        (op(Q, 'inc'), 4), (op(Q, 'decnz'), 12, 2),
        (op(F, 'inc'), 11), (op(B, 'decnz'), 14, 15), (op(K, 'inc'), 13)]
    mapping, incoming, outgoing = locate(graph.rows, clock_spec)
    zero = lambda entry, names: all(invariant['states_at_occurrences'][graph.indices[entry]][grammar['registers'].index(name)] == '1' for name in names)
    assert zero(mapping[0], (B, Q, C)), 'clock scratch not proved zero at actual entry'
    cases = [(n, k, stale) for n in range(5) for k in range(5) for stale in (0, 3, 19)]
    cases += [(2 ** 100 + 7, 0, 11), (0, 257, 9), (1, 9, 0)]
    total = 0
    for n, k, stale in cases:
        before = {name: 100 + i for i, name in enumerate(grammar['registers'])}
        before.update({F: stale, N: n, K: k, B: 0, Q: 0, C: 0})
        after, steps = execute(graph.rows, mapping[0], mapping[15], before)
        expected = dict(before)
        expected[F] = (n + 1) ** k
        assert after == expected and steps > 0
        total += steps
    clock_result = dict(rows=15, entry=''.join(map(str, mapping[0])),
        entry_zero_carriers=[B, Q, C], logical_carriers=[F, N, K, B, Q, C],
        physical_carriers=[sharing[x] for x in (F, N, K, B, Q, C)],
        sole_ingress_targets=1, outside_ingress_edges=len(incoming), outside_exit_edges=len(outgoing),
        fixtures=len(cases), primitive_steps=total)
    clock_bad = deepcopy(graph.rows)
    clock_bad[mapping[14]] = (op(F, 'inc'), mapping[13])
    try:
        locate(clock_bad, clock_spec)
    except AssertionError:
        pass
    else:
        raise AssertionError('damaged clock restoration accepted')

    F, S, K, Q = [actual_name(seed[key]) for key in ('output', 'restore_counter', 'clock_master', 'double_work')]
    assert len({F, S, K, Q}) == len({sharing[x] for x in (F, S, K, Q)}) == 4
    seed_spec = [(op(F, 'decnz'), 0, 1), (op(F, 'inc'), 2),
        (op(K, 'decnz'), 3, 9), (op(S, 'inc'), 4),
        (op(F, 'decnz'), 5, 7), (op(Q, 'inc'), 6), (op(Q, 'inc'), 4),
        (op(Q, 'decnz'), 8, 2), (op(F, 'inc'), 7),
        (op(S, 'decnz'), 10, 11), (op(K, 'inc'), 9)]
    mapping, incoming, outgoing = locate(graph.rows, seed_spec)
    assert zero(mapping[0], (S, Q)), 'seed work or elided reset target not zero at actual entry'
    total = 0
    for k in range(11):
        for stale in (0, 3, 19):
            before = {name: 200 + i for i, name in enumerate(grammar['registers'])}
            before.update({F: stale, S: 0, K: k, Q: 0})
            after, steps = execute(graph.rows, mapping[0], mapping[11], before)
            expected = dict(before)
            expected[F] = 1 << k
            assert after == expected and steps > 0
            total += steps
    seed_result = dict(rows=11, entry=''.join(map(str, mapping[0])),
        entry_zero_carriers=[S, Q], logical_carriers=[F, S, K, Q],
        physical_carriers=[sharing[x] for x in (F, S, K, Q)],
        sole_ingress_targets=1, outside_ingress_edges=len(incoming), outside_exit_edges=len(outgoing),
        fixtures=33, primitive_steps=total)
    seed_bad = deepcopy(graph.rows)
    seed_bad[mapping[6]] = (op(S, 'inc'), mapping[4])
    try:
        locate(seed_bad, seed_spec)
    except AssertionError:
        pass
    else:
        raise AssertionError('damaged seed doubling accepted')
    return dict(schema='npconp-transfer-independent-closed-regions-v1', **summary,
        clock=clock_result, certificate_seed=seed_result,
        damaged_rows_rejected=['clock exponent restoration', 'certificate doubling'],
        inputs={name: sha(parent / name) for name in ('pre-coalescence-grammar.json',
            'allocation.json', 'bank-coalescence.json', 'coalescence-invariant.json',
            'direct-clock.json', 'certificate-seed.json')},
        scope='Independent actual tuple paths, all supplied abstract closure edges and ordinary-operation zero peers, closed region entries/exits, entry-zero masks and finite fixtures; not literal binary execution')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--parent', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    result = run(args.parent)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps(result, sort_keys=True, indent=2))
