"""Measured control-grammar reassociation; never credit a grammar count alone.

The all-branch graph construction and rotation idea are adapted from the PA
lane's grammar_search.py at 1c2a3c8b42a727b0d4d29a4ee95b90ff9b22ce97,
whose exact source is preserved under scout/upstream.  No PA theorem transfers.
Every accepted rotation must preserve each primitive occurrence and both
DECNZ successors, including explicit breaks and loop restarts.
"""
from collections import Counter
from contextlib import contextmanager
from copy import copy
from pathlib import Path
import argparse
import hashlib
import json

import integrated
from TMBuilder import Sequence


def graph(builder):
    root = builder.find_seq('main().0')
    leaves, starts = [], {}
    def visit(node, path, ancestors):
        starts[path] = len(leaves)
        if type(node) is int:
            if node in ancestors:
                raise ValueError('cyclic control grammar')
            a, b = builder.sequences[node].seq
            visit(a, path+(0,), ancestors | {node})
            visit(b, path+(1,), ancestors | {node})
        else:
            leaves.append((path, node))
    visit(root, (1, 1, 0), set())
    def resolve(path):
        if path == (1, 1) or path[:3] == (1, 1, 1):
            return 0
        return starts[path]
    def successor(path, skip):
        for i in range(len(path)-1, 1, -1):
            if path[i] == 0:
                if skip == 0:
                    return resolve(path[:i]+(1,))
                skip -= 1
        raise ValueError(('successor crosses root', path, skip))
    def restart(path, skip):
        for i in range(len(path)-1, 0, -1):
            if path[i] == 1:
                if skip == 0:
                    return resolve(path[:i+1])
                skip -= 1
        raise ValueError(('restart crosses root', path, skip))
    rows = []
    for path, op in leaves:
        if op.startswith('_break.'):
            rows.append(('jump', successor(path, int(op.split('.')[1]))))
        elif op.startswith('_continue.'):
            rows.append(('jump', restart(path, int(op.split('.')[1]))))
        elif op.endswith('.decnz'):
            rows.append((op, successor(path, 0), successor(path, 1)))
        else:
            rows.append((op, successor(path, 0)))
    return rows


def digest(value):
    return hashlib.sha256(json.dumps(value, separators=(',', ':')).encode()).hexdigest()


def metric(builder):
    cache = {}
    def depth(node, ancestors):
        if type(node) is not int:
            return 0
        if node in ancestors:
            raise ValueError('cyclic control grammar')
        if node not in cache:
            cache[node] = 1+max(depth(child, ancestors | {node})
                                for child in builder.sequences[node].seq)
        return cache[node]
    height = depth(builder.find_seq('main().0'), set())
    return len(cache), height


def clone(builder):
    result = copy(builder)
    result.sequences = [copy(sequence) for sequence in builder.sequences]
    return result


def patterns(builder):
    counts = Counter()
    present = {tuple(s.seq) for s in builder.sequences}
    for i in builder.reachable():
        a, b = builder.sequences[i].seq
        if type(b) is int:
            c, _ = builder.sequences[b].seq
            counts['R', a, c] += 1
        if type(a) is int:
            _, c = builder.sequences[a].seq
            counts['L', c, b] += 1
    return [p for p, n in sorted(counts.items(), key=lambda p: (-p[1], str(p[0])))
            if n >= 2 or p[1:] in present]


def rotate(builder, pattern):
    direction, a, c = pattern
    intern = {tuple(s.seq): i for i, s in enumerate(builder.sequences)}
    key = (a, c)
    matches = []
    for i in sorted(builder.reachable()):
        x, y = builder.sequences[i].seq
        if direction == 'R' and x == a and type(y) is int:
            v, w = builder.sequences[y].seq
            if v == c:
                matches.append((i, w))
        elif direction == 'L' and y == c and type(x) is int:
            v, w = builder.sequences[x].seq
            if w == a:
                matches.append((i, v))
    if not matches:
        raise ValueError(('unmatched rotation', pattern))
    if key not in intern:
        intern[key] = len(builder.sequences)
        builder.sequences.append(Sequence(key))
    inner = intern[key]
    for i, z in matches:
        builder.sequences[i].seq = (inner, z) if direction == 'R' else (z, inner)
    return len(matches)


def search(builder, rounds=12):
    original = graph(builder)
    baseline = metric(builder)
    current, moves, rejected, tested = builder, [], [], 0
    for _ in range(rounds):
        best = None
        old = metric(current)
        for pattern in patterns(current):
            candidate = clone(current)
            occurrences = rotate(candidate, pattern)
            try:
                measured = metric(candidate)
            except ValueError:
                continue
            if (sum(measured), measured) >= (sum(old), old):
                continue
            tested += 1
            try:
                valid = graph(candidate) == original
            except (ValueError, KeyError):
                valid = False
            if not valid:
                if len(rejected) < 12:
                    rejected.append(pattern)
                continue
            score = (sum(measured), measured)
            if best is None or score < best[0]:
                best = (score, candidate, pattern, occurrences)
        if best is None:
            break
        _, current, pattern, occurrences = best
        moves.append(pattern)
        print(json.dumps(dict(move=pattern, occurrences=occurrences,
                              metric=metric(current))), flush=True)
    assert graph(current) == original
    return dict(format='np-conp-all-branch-rotations-v1',
                graph_sha256=digest(original), unfolded_leaves=len(original),
                before=list(baseline), after=list(metric(current)), moves=moves,
                tested_improving_candidates=tested, rejected_examples=rejected)


def apply(builder, plan):
    before = graph(builder)
    assert digest(before) == plan['graph_sha256']
    assert len(before) == plan['unfolded_leaves']
    assert list(metric(builder)) == plan['before']
    for pattern in plan['moves']:
        rotate(builder, pattern)
    builder.name_sequences()
    assert graph(builder) == before
    assert list(metric(builder)) == plan['after']


@contextmanager
def installed(plan):
    original = integrated.build_live.HalfPairBuilder
    class Rotated(original):
        def build_tree(self):
            super().build_tree()
            apply(self, plan)
            return self
    integrated.build_live.HalfPairBuilder = Rotated
    try:
        yield
    finally:
        integrated.build_live.HalfPairBuilder = original


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--plan', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--rounds', type=int, default=12)
    args = parser.parse_args()
    if args.plan.exists() or args.out.exists():
        raise ValueError('fresh output paths required')
    source = integrated.HERE/'source/forced_relative.py'
    options = dict(lookup=False, pair_half=True, options={'affine_assignments': False})
    builder, *_ = integrated.construct(source, **options)
    plan = search(builder, args.rounds)
    plan['source_sha256'] = hashlib.sha256(source.read_bytes()).hexdigest()
    plan['options'] = options
    args.plan.write_text(json.dumps(plan, sort_keys=True, indent=2)+'\n')
    with integrated.installed(**options), installed(plan):
        result = integrated.build_live.build(args.out, source)
    print(json.dumps({key: result[key] for key in ('event_states', 'states', 'raw_states',
        'profile', 'event_table_sha256')}, indent=2))
