"""Search and replay paid control-grammar rotations.

The proof obligation is equality of the full unfolded primitive control graph,
including both outcomes of each decrement.  Unlike the old height heuristic,
the score charges the left depth that generates physical dispatch states.
Search is an experiment; a selected producer replays a fixed checked plan.
"""
from collections import Counter
from contextlib import contextmanager
from pathlib import Path
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent/'arithmetic'))
import integrated
import grammar_rotations as prior
from TMBuilder import Sequence


def normalize(builder):
    """Re-intern identical pairs, retaining the expanded ordered tree exactly."""
    nodes, memo, pairs, pending = [], {}, {}, set()
    def visit(value):
        if type(value) is not int:
            return value
        if value in pending:
            raise ValueError('cyclic grammar')
        if value in memo:
            return memo[value]
        pending.add(value)
        pair = tuple(visit(v) for v in builder.sequences[value].seq)
        pending.remove(value)
        if pair not in pairs:
            pairs[pair] = len(nodes)
            nodes.append(Sequence(pair))
        memo[value] = pairs[pair]
        return memo[value]
    root = visit(builder.find_seq('main().0'))
    builder.sequences = nodes
    builder.sequence_lookup = pairs
    for i, node in enumerate(nodes):
        node.name = 'main().0' if i == root else f'compact_grammar_{i}.0'
    return root


def metric(builder):
    seen, pending = {}, set()
    def visit(value):
        if type(value) is not int:
            return 0, 0
        if value in pending:
            raise ValueError('cyclic grammar')
        if value not in seen:
            pending.add(value)
            (hl, zl), (hr, zr) = map(visit, builder.sequences[value].seq)
            pending.remove(value)
            seen[value] = 1 + max(hl, hr), max(1 + zl, zr)
        return seen[value]
    height, zeros = visit(builder.find_seq('main().0'))
    return len(seen), zeros, height


def score(builder):
    nodes, zeros, height = metric(builder)
    return nodes + zeros, nodes, zeros, height


def patterns(builder, broad=False):
    counts = Counter()
    present = {tuple(s.seq) for s in builder.sequences}
    for i in sorted(builder.reachable()):
        a, b = builder.sequences[i].seq
        if type(b) is int:
            c, _ = builder.sequences[b].seq
            counts['R', a, c] += 1
        if type(a) is int:
            _, c = builder.sequences[a].seq
            counts['L', c, b] += 1
    return [p for p, n in sorted(counts.items(), key=lambda p: (-p[1], str(p[0])))
            if broad or n >= 2 or p[1:] in present]


def trial(builder, pattern):
    candidate = prior.clone(builder)
    occurrences = prior.rotate(candidate, pattern)
    normalize(candidate)
    return candidate, occurrences


def search(builder, rounds=60, broad=False):
    original = prior.graph(builder)
    before = list(metric(builder))
    current = prior.clone(builder)
    normalize(current)
    normalized = list(metric(current))
    assert prior.graph(current) == original
    moves, examined, rejected = [], 0, 0
    for _ in range(rounds):
        best = None
        old = score(current)
        for pattern in patterns(current, broad):
            examined += 1
            try:
                candidate, occurrences = trial(current, pattern)
                measured = score(candidate)
                if measured >= old:
                    continue
                valid = prior.graph(candidate) == original
            except (ValueError, KeyError, RecursionError):
                valid = False
            if not valid:
                rejected += 1
                continue
            if best is None or measured < best[0]:
                best = measured, candidate, pattern, occurrences
        if best is None:
            break
        _, current, pattern, occurrences = best
        moves.append(pattern)
        print(json.dumps(dict(move=pattern, occurrences=occurrences,
                              metric=metric(current))), flush=True)
    assert prior.graph(current) == original
    return dict(format='np-conp-zero-depth-grammar-v1',
                graph_sha256=prior.digest(original), unfolded_leaves=len(original),
                before=before, normalized=normalized, after=list(metric(current)),
                moves=moves, examined=examined, rejected_graph_changes=rejected,
                metric='reachable pair nodes + maximum left depth; then nodes, left depth, height',
                broad_patterns=broad)


def apply(builder, plan):
    original = prior.graph(builder)
    assert prior.digest(original) == plan['graph_sha256']
    assert len(original) == plan['unfolded_leaves']
    assert list(metric(builder)) == plan['before']
    normalize(builder)
    assert list(metric(builder)) == plan['normalized']
    for move in plan['moves']:
        prior.rotate(builder, move)
        normalize(builder)
        assert prior.graph(builder) == original
    assert list(metric(builder)) == plan['after']
    assert prior.graph(builder) == original


@contextmanager
def installed(plan):
    original = integrated.build_live.HalfPairBuilder
    class CompactGrammar(original):
        def build_tree(self):
            super().build_tree()
            self.compact_input_grammar = integrated.build_live.baseline.grammar(self)
            apply(self, plan)
            self.compact_grammar_plan = plan
            return self
    integrated.build_live.HalfPairBuilder = CompactGrammar
    try:
        yield
    finally:
        integrated.build_live.HalfPairBuilder = original


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--source', type=Path)
    parser.add_argument('--rounds', type=int, default=60)
    parser.add_argument('--broad', action='store_true')
    parser.add_argument('--direct-calls', action='store_true')
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError('fresh output required')
    sys.path.insert(0, str(HERE.parent/'arithmetic/compiler'))
    from mixed_tuples import installed as mixed_runtime
    from contextlib import nullcontext
    source = args.source or HERE.parent/'arithmetic/source/forced_relative.py'
    options = dict(lookup=False, pair_half=True,
                   options={'affine_assignments': False, 'affine_forward': False})
    if args.direct_calls:
        sys.path.insert(0, str(HERE/'compiler'))
        import direct_calls
        call_context = direct_calls.installed
    else:
        call_context = lambda *args: nullcontext()
    with mixed_runtime(integrated), call_context(integrated):
        builder, *_ = integrated.construct(source, **options)
        plan = search(builder, args.rounds, args.broad)
        plan['source_sha256'] = hashlib.sha256(source.read_bytes()).hexdigest()
        with integrated.installed(**options), installed(plan):
            result = integrated.build_live.build(args.out, source)
    integrated.build_live.baseline.dump(args.out/'compact-grammar-plan.json', plan)
    print(json.dumps({k: result[k] for k in ('event_states', 'states', 'raw_states',
        'registers', 'profile', 'event_table_sha256')}, indent=2))
