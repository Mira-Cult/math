#!/usr/bin/env python3
"""Price context-rebound control sharing over the clean-boundary architecture.

The search ceiling is a resource bound, not an optimality assertion.  Every
accepted step keeps all ordered primitive, decrement, event and resolved jump
edges.  Source and backend are unchanged; only the paid control representation
is searched.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from collections import Counter
from pathlib import Path

import rebind_grammar as first
import clean_boundaries


class Base(first.total_preparation.TotalPreparation, first.run_dispatch.RunDispatch,
           clean_boundaries.CleanBoundaries):
    pass

ROOT = Path(__file__).resolve().parent
PLAN = ROOT / 'clean-rebind-plan.json'
p = first.p


def score(priced):
    boot = priced['ledger']['boot']
    return (boot['selected'], priced['grammar_nodes'],
            boot['ledger']['engine-and-totalization'],
            priced['run_dispatch']['max_zero_run'],
            priced['ledger']['counted']['selected'])


def search(max_passes=96, max_candidates=30000):
    builder = Base(p.opt.SOURCE)
    builder.build_tree()
    original = p.gs.graph(builder)
    baseline = selected = first.price(builder)
    accepted, examples, prices = [], [], []
    rejected = Counter()
    cache = {first.structure(builder): selected}
    tested = valid = complete_passes = 0
    plateau = False
    for pass_index in range(max_passes):
        best = None
        exhausted = True
        for pattern in first.patterns(builder):
            if tested >= max_candidates:
                exhausted = False
                break
            tested += 1
            candidate = copy.deepcopy(builder)
            try:
                first.rotate(candidate, pattern)
                changed = first.rebind(candidate, original)
            except (first.RebindFailure, ValueError, KeyError, RecursionError) as error:
                reason = str(error)
                rejected[reason] += 1
                if len(examples) < 32:
                    examples.append({'pattern': pattern, 'reason': reason})
                continue
            valid += 1
            key = first.structure(candidate)
            if key not in cache:
                cache[key] = first.price(candidate)
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
                         'structure_sha256': first.structure(builder), 'price': selected})
        print(json.dumps({'pass': pass_index + 1, 'tested': tested, 'valid': valid,
                          'selected': score(selected), 'rebound': changed,
                          'pattern': pattern}), flush=True)
        if not exhausted:
            break
    assert p.gs.graph(builder) == original
    inputs = first.input_hashes()
    return {
        'format': 'context-rebound-clean-boundaries-paid-v1',
        'source_class': 'CleanBoundaries',
        'score_order': ['boot quotient', 'grammar', 'runtime', 'zero run', 'counted quotient'],
        'inputs': inputs, 'baseline_price': baseline, 'selected_price': selected,
        'graph_sha256': p.gs.digest(original), 'primitive_occurrences': len(original),
        'control_edges': sum(len(row) - 1 for row in original),
        'accepted': accepted, 'tested_candidates': tested, 'valid_candidates': valid,
        'distinct_complete_prices': prices, 'rejection_counts': dict(rejected),
        'rejected_examples': examples, 'complete_passes': complete_passes,
        'max_passes': max_passes, 'max_candidates': max_candidates,
        'stopped_at_restricted_plateau': plateau,
    }


class ReboundClean(Base):
    def build_tree(self):
        super().build_tree()
        original = p.gs.graph(self)
        plan = json.loads(PLAN.read_text())
        for relative, expected in plan['inputs'].items():
            assert hashlib.sha256((first.REPO / relative).read_bytes()).hexdigest() == expected, relative
        assert p.gs.digest(original) == plan['graph_sha256']
        for change in plan['accepted']:
            first.rotate(self, change['pattern'])
            assert first.rebind(self, original) == change['rebound_transfer_occurrences']
            assert first.structure(self) == change['structure_sha256']
        assert p.gs.graph(self) == original
        return self


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--search', action='store_true')
    parser.add_argument('--max-passes', type=int, default=96)
    parser.add_argument('--max-candidates', type=int, default=30000)
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
        builder, ledger, _ = p.opt.compile_candidate(ReboundClean, args.out)
        assert ledger == json.loads(PLAN.read_text())['selected_price']['ledger']
        (args.out / 'run-dispatch.json').write_text(json.dumps(builder.run_dispatch_certificate,
                                                            sort_keys=True, indent=2) + '\n')
        print(json.dumps(ledger, indent=2))
    elif not args.search:
        parser.error('--search or --out required')
