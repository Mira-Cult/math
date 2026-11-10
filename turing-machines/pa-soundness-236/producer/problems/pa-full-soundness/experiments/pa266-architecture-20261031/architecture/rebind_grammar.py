#!/usr/bin/env python3
"""Reassociate grammar, rebind transfer levels, and price every valid candidate.

All primitive/decrement/event edges must remain identical. Relative break and
continue leaves may be re-encoded for their original target; occurrence-wise
rebuilding then shares only literally identical resulting subtrees. Every
accepted candidate is charged with the actual run-dispatch binary backend.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import sys
import tempfile
from collections import Counter
from pathlib import Path

import ordered_cantor
import run_dispatch
import total_preparation
from TMBuilder import Sequence

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[4]
sys.path.insert(0, str(ROOT.parents[1] / 'pa800-grammar'))
from reassociate import rotate

p = ordered_cantor.p
PLAN = ROOT / 'rebind-grammar-plan.json'


class Base(total_preparation.TotalPreparation, run_dispatch.RunDispatch,
           ordered_cantor.StrictCantor):
    pass


class RebindFailure(ValueError):
    pass


def rebind(builder, original):
    root = builder.find_seq('main().0')
    leaves, starts = [], {}

    def unfold(node, path):
        starts[path] = len(leaves)
        if type(node) is int:
            left, right = builder.sequences[node].seq
            unfold(left, path + (0,))
            unfold(right, path + (1,))
        else:
            leaves.append((path, node))
    unfold(root, (1, 1, 0))
    if len(leaves) != len(original):
        raise RebindFailure('leaf-count')

    def resolve(path):
        return 0 if path == (1, 1) or path[:3] == (1, 1, 1) else starts[path]

    def successor(path, level):
        for i in range(len(path) - 1, 1, -1):
            if path[i] == 0:
                if level == 0:
                    return resolve(path[:i] + (1,))
                level -= 1
        raise RebindFailure('successor-outside-sentinel')

    def restart(path, level):
        for i in range(len(path) - 1, 0, -1):
            if path[i] == 1:
                if level == 0:
                    return resolve(path[:i + 1])
                level -= 1
        raise RebindFailure('restart-outside-sentinel')

    replacements, changed = {}, 0
    for index, (path, operation) in enumerate(leaves):
        target = original[index]
        if not operation.startswith(('_break.', '_continue.')):
            row = (operation, successor(path, 0))
            if operation.endswith('.decnz'):
                row += (successor(path, 1),)
            if row != target:
                raise RebindFailure('decrement-outcome' if operation.endswith('.decnz') else 'primitive-edge')
            replacements[path] = operation
            continue
        if target[0] != 'jump':
            raise RebindFailure('transfer-kind')
        choices = []
        for kind, resolver in (('_break.', successor), ('_continue.', restart)):
            for level in range(len(path) + 1):
                # The binary generator excludes continue.0 in a right child.
                if kind == '_continue.' and level == 0 and path[-1] == 1:
                    continue
                try:
                    destination = resolver(path, level)
                except (RebindFailure, KeyError):
                    continue
                if destination == target[1]:
                    choices.append(kind + str(level))
        if not choices:
            raise RebindFailure('unrepresentable-transfer')
        # Preserve an already-valid encoding; otherwise use the shortest level.
        chosen = operation if operation in choices else min(
            choices, key=lambda value: (int(value.split('.')[1]), value))
        changed += chosen != operation
        replacements[path] = chosen

    sequences, lookup = [], {}
    def rebuild(node, path):
        if type(node) is not int:
            return replacements[path]
        left, right = builder.sequences[node].seq
        key = (rebuild(left, path + (0,)), rebuild(right, path + (1,)))
        if key not in lookup:
            lookup[key] = len(sequences)
            sequences.append(Sequence(key))
        return lookup[key]
    new_root = rebuild(root, (1, 1, 0))
    for index, sequence in enumerate(sequences):
        sequence.name = 'main().0' if index == new_root else f'rebound_{index}.0'
    builder.sequences = sequences
    builder.sequence_lookup = lookup
    builder.memo = {}
    if p.gs.graph(builder) != original:
        raise RebindFailure('post-rebuild-graph')
    return changed


def patterns(builder):
    counts = Counter()
    for index in sorted(builder.reachable()):
        left, right = builder.sequences[index].seq
        if type(right) is int:
            first, _ = builder.sequences[right].seq
            counts['R', left, first] += 1
        if type(left) is int:
            _, last = builder.sequences[left].seq
            counts['L', last, right] += 1
    return [pattern for pattern, _ in sorted(counts.items(), key=lambda row: (-row[1], str(row[0])))]


def structure(builder):
    return hashlib.sha256(json.dumps([sequence.seq for sequence in builder.sequences],
                                     separators=(',', ':')).encode()).hexdigest()


def price(builder):
    class Priced(Base):
        def build_tree(self):
            snapshot = copy.deepcopy(builder)
            self.__dict__.clear()
            self.__dict__.update(snapshot.__dict__)
            return self
    with tempfile.TemporaryDirectory(prefix='pa-rebind-price-') as temp:
        physical, ledger, _ = p.opt.compile_candidate(Priced, Path(temp) / 'machine')
    return {'ledger': ledger, 'run_dispatch': physical.run_dispatch_certificate,
            'grammar_nodes': len(list(builder.reachable()))}


def score(priced):
    return (priced['ledger']['boot']['selected'], priced['ledger']['counted']['selected'],
            priced['grammar_nodes'], priced['run_dispatch']['max_zero_run'])


def input_hashes():
    paths = {Path(module.__file__).resolve() for module in tuple(sys.modules.values())
             if getattr(module, '__file__', None)
             and Path(module.__file__).resolve().is_relative_to(REPO)
             and Path(module.__file__).suffix == '.py'}
    paths.add(p.opt.ROOT / 'baseline/code/compact/source.py')
    return {str(path.relative_to(REPO)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(paths)}


def search(max_passes=16, max_candidates=4000):
    builder = Base(p.opt.SOURCE)
    builder.build_tree()
    original = p.gs.graph(builder)
    baseline = selected = price(builder)
    accepted, examples, prices = [], [], []
    rejected = Counter()
    cache = {}
    tested = valid = complete_passes = 0
    plateau = False
    for pass_index in range(max_passes):
        best = None
        exhausted = True
        for pattern in patterns(builder):
            if tested >= max_candidates:
                exhausted = False
                break
            tested += 1
            candidate = copy.deepcopy(builder)
            try:
                rotate(candidate, pattern)
                changed = rebind(candidate, original)
            except (RebindFailure, ValueError, KeyError, RecursionError) as error:
                reason = str(error)
                rejected[reason] += 1
                if len(examples) < 32:
                    examples.append({'pattern': pattern, 'reason': reason})
                continue
            valid += 1
            key = structure(candidate)
            if key not in cache:
                cache[key] = price(candidate)
                prices.append({'structure_sha256': key, 'price': cache[key]})
            candidate_price = cache[key]
            if score(candidate_price) >= score(selected):
                continue
            if best is None or score(candidate_price) < score(best[3]):
                best = candidate, pattern, changed, candidate_price
        complete_passes += exhausted
        if best is None:
            plateau = exhausted
            break
        builder, pattern, changed, selected = best
        accepted.append({'pattern': pattern, 'rebound_transfer_occurrences': changed,
                         'structure_sha256': structure(builder), 'price': selected})
        print(json.dumps({'pass': pass_index + 1, 'tested': tested, 'valid': valid,
                          'selected': score(selected), 'rebound': changed,
                          'pattern': pattern}), flush=True)
        if not exhausted:
            break
    assert p.gs.graph(builder) == original
    return {
        'format': 'context-rebound-full-graph-paid-grammar-v1',
        'source_class': 'StrictCantor', 'backend': ['RunDispatch', 'TotalPreparation'],
        'inputs': input_hashes(), 'baseline_price': baseline, 'selected_price': selected,
        'graph_sha256': p.gs.digest(original), 'primitive_occurrences': len(original),
        'control_edges': sum(len(row) - 1 for row in original),
        'accepted': accepted, 'tested_candidates': tested, 'valid_candidates': valid,
        'distinct_complete_prices': prices, 'rejection_counts': dict(rejected),
        'rejected_examples': examples, 'complete_passes': complete_passes,
        'max_passes': max_passes, 'max_candidates': max_candidates,
        'stopped_at_restricted_plateau': plateau,
    }


class ReboundGrammar(Base):
    def build_tree(self):
        super().build_tree()
        original = p.gs.graph(self)
        plan = json.loads(PLAN.read_text())
        for relative, expected in plan['inputs'].items():
            assert hashlib.sha256((REPO / relative).read_bytes()).hexdigest() == expected, relative
        assert p.gs.digest(original) == plan['graph_sha256']
        for change in plan['accepted']:
            rotate(self, change['pattern'])
            assert rebind(self, original) == change['rebound_transfer_occurrences']
            assert structure(self) == change['structure_sha256']
        assert p.gs.graph(self) == original
        return self


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--search', action='store_true')
    parser.add_argument('--max-passes', type=int, default=16)
    parser.add_argument('--max-candidates', type=int, default=4000)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    if args.search:
        if PLAN.exists():
            raise ValueError('Refusing to overwrite a fixed plan')
        plan = search(args.max_passes, args.max_candidates)
        PLAN.write_text(json.dumps(plan, sort_keys=True, indent=2) + '\n')
        print(json.dumps({key: value for key, value in plan.items()
                          if key not in ('inputs', 'distinct_complete_prices', 'rejected_examples', 'accepted')}, indent=2))
    if args.out:
        if args.out.exists():
            raise ValueError('Fresh output directory required')
        builder, ledger, _ = p.opt.compile_candidate(ReboundGrammar, args.out)
        assert ledger == json.loads(PLAN.read_text())['selected_price']['ledger']
        (args.out / 'run-dispatch.json').write_text(json.dumps(builder.run_dispatch_certificate,
                                                            sort_keys=True, indent=2) + '\n')
        print(json.dumps(ledger, indent=2))
    elif not args.search:
        parser.error('--search or --out required')
