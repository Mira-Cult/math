"""Measured removal of finite administrative control paths.

Every candidate preserves both branches of every register decrement and each
ordered register/event occurrence after finite jump-chain contraction.  Any
jump-only cycle is rejected, even when it appears unreachable.  The selected
plan, if any, is replayed with these complete finite certificates.
"""
from pathlib import Path
from contextlib import contextmanager
import argparse
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import grammar


def core_graph(builder):
    full = grammar.prior.graph(builder)
    retained = [i for i, row in enumerate(full) if row[0] != 'jump']
    numbering = {old: new for new, old in enumerate(retained)}
    if not retained:
        raise ValueError('no retained primitive')
    chains = {}
    def target(index):
        path, seen = [], set()
        while full[index][0] == 'jump':
            if index in seen:
                raise ValueError('administrative jump cycle')
            seen.add(index)
            path.append(index)
            index = full[index][1]
        for old in path:
            chains[old] = index
        return numbering[index]
    # Check ALL jumps, including any absent from the chosen start trajectory.
    for index, row in enumerate(full):
        if row[0] == 'jump':
            target(index)
    rows = [(full[index][0], *(target(x) for x in full[index][1:]))
            for index in retained]
    return dict(entry=target(0), rows=rows)


def drop(builder, node, side):
    child = builder.sequences[node].seq[side]
    root = builder.find_seq('main().0')
    if node == root:
        if type(child) is not int:
            raise ValueError('nontrivial root required')
        builder.sequences[node].name = None
        builder.sequences[child].name = 'main().0'
    for sequence in builder.sequences:
        sequence.seq = tuple(child if value == node else value
                             for value in sequence.seq)
    grammar.normalize(builder)


def actions(builder, broad=False):
    for pattern in grammar.patterns(builder, broad):
        yield ['rotate', *pattern]
    pure = {}
    def only_jump(value):
        if type(value) is not int:
            return value.startswith('_break.') or value.startswith('_continue.')
        if value not in pure:
            pure[value] = all(only_jump(x) for x in builder.sequences[value].seq)
        return pure[value]
    for i in sorted(builder.reachable()):
        left, right = builder.sequences[i].seq
        if only_jump(left):
            yield ['drop', i, 1]
        if only_jump(right):
            yield ['drop', i, 0]


def act(builder, action):
    if action[0] == 'rotate':
        grammar.prior.rotate(builder, action[1:])
        grammar.normalize(builder)
    elif action[0] == 'drop':
        drop(builder, *action[1:])
    else:
        raise ValueError(action)


def search(builder, rounds=80, broad=False):
    original = core_graph(builder)
    current = grammar.prior.clone(builder)
    before = list(grammar.metric(current))
    grammar.normalize(current)
    normalized = list(grammar.metric(current))
    assert core_graph(current) == original
    moves, examined, rejected = [], 0, 0
    best_cut, paid_score = 0, grammar.score(current)[:3]
    for _ in range(rounds):
        best = None
        old = grammar.score(current)
        for action in actions(current, broad):
            examined += 1
            candidate = grammar.prior.clone(current)
            try:
                act(candidate, action)
                measured = grammar.score(candidate)
                if measured >= old:
                    continue
                valid = core_graph(candidate) == original
            except (ValueError, KeyError, RecursionError):
                valid = False
            if not valid:
                rejected += 1
                continue
            if best is None or measured < best[0]:
                best = measured, candidate, action
        if best is None:
            break
        _, current, action = best
        moves.append(action)
        if grammar.score(current)[:3] < paid_score:
            best_cut, paid_score = len(moves), grammar.score(current)[:3]
        print(json.dumps(dict(action=action, metric=grammar.metric(current))), flush=True)
    # Height-only trailing moves gave no paid saving.  Do not burden the frozen
    # producer with them; useful neutral moves preceding a saving are retained.
    discarded = len(moves) - best_cut
    moves = moves[:best_cut]
    current = grammar.prior.clone(builder)
    grammar.normalize(current)
    for action in moves:
        act(current, action)
    assert core_graph(current) == original
    return dict(format='np-conp-finite-jump-contraction-v1',
                graph_sha256=grammar.prior.digest(original),
                retained_primitives=len(original['rows']),
                before=before, normalized=normalized, after=list(grammar.metric(current)),
                moves=moves, examined=examined, rejected_graph_changes=rejected,
                discarded_trailing_height_only_moves=discarded,
                metric='pair nodes + left depth, then nodes, left depth, height',
                relation='ordered INC/DECNZ/beep with both DECNZ outcomes; finite control steps may differ',
                all_jump_only_cycles_rejected=True, broad_patterns=broad)


def apply(builder, plan):
    original = core_graph(builder)
    assert grammar.prior.digest(original) == plan['graph_sha256']
    assert len(original['rows']) == plan['retained_primitives']
    assert list(grammar.metric(builder)) == plan['before']
    grammar.normalize(builder)
    assert list(grammar.metric(builder)) == plan['normalized']
    for action in plan['moves']:
        act(builder, action)
        assert core_graph(builder) == original
    assert list(grammar.metric(builder)) == plan['after']


@contextmanager
def installed(plan):
    original = grammar.integrated.build_live.HalfPairBuilder
    class WeakGrammar(original):
        def build_tree(self):
            super().build_tree()
            self.weak_input_grammar = grammar.integrated.build_live.baseline.grammar(self)
            apply(self, plan)
            self.weak_grammar_plan = plan
            return self
    grammar.integrated.build_live.HalfPairBuilder = WeakGrammar
    try:
        yield
    finally:
        grammar.integrated.build_live.HalfPairBuilder = original


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--source', required=True, type=Path)
    parser.add_argument('--rounds', type=int, default=80)
    parser.add_argument('--broad', action='store_true')
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError('fresh output required')
    sys.path.insert(0, str(HERE/'compiler'))
    import build_compact
    builder, *_ = build_compact.construct(args.source)
    plan = search(builder, args.rounds, args.broad)
    plan['source_sha256'] = build_compact.integrated.build_live.baseline.sha(args.source)
    with build_compact.installed(), installed(plan):
        metadata = build_compact.integrated.build_live.build(args.out, args.source)
    build_compact.integrated.build_live.baseline.dump(args.out/'weak-grammar-plan.json', plan)
    print(json.dumps({key: metadata[key] for key in
        ('raw_states', 'states', 'event_states', 'registers', 'profile', 'event_table_sha256')}, indent=2))
