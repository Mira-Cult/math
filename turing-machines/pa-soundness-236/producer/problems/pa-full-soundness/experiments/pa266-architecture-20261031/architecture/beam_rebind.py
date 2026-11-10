#!/usr/bin/env python3
"""Bounded paid sideways search from the frozen complete 240-state grammar.

Every visited candidate uses exact resolved primitive graph preservation.
The beam permits one temporary complete state above the starting machine;
it grants no source-code or runtime omission when pricing those candidates.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from collections import Counter
from pathlib import Path

import clean_rebind as parent

ROOT = Path(__file__).resolve().parent
PLAN = ROOT / 'beam-rebind-plan.json'
first = parent.first
p = first.p


def compact_price(key, price):
    boot, counted = price['ledger']['boot'], price['ledger']['counted']
    return [key, boot['raw'], boot['selected'], counted['raw'], counted['selected'],
            price['grammar_nodes'], boot['ledger']['engine-and-totalization'],
            price['run_dispatch']['max_zero_run']]


def search(max_depth=12, beam_width=16, max_candidates=30000, allowance=1):
    builder = parent.ReboundClean(p.opt.SOURCE)
    builder.build_tree()
    original = p.gs.graph(builder)
    baseline = selected = first.price(builder)
    selected_path = []
    key = first.structure(builder)
    seen = {key}
    frontier = [(builder, [], baseline, key)]
    ceiling = baseline['ledger']['boot']['selected'] + allowance
    tested = valid = complete_depths = 0
    rejected = Counter()
    receipts, depth_reports = [], []
    stopped = 'depth bound'
    for depth in range(1, max_depth + 1):
        pool = []
        exhausted = True
        for node, path, _, _ in frontier:
            for pattern in first.patterns(node):
                if tested >= max_candidates:
                    exhausted = False
                    break
                tested += 1
                candidate = copy.deepcopy(node)
                try:
                    first.rotate(candidate, pattern)
                    changed = first.rebind(candidate, original)
                except (first.RebindFailure, ValueError, KeyError, RecursionError) as error:
                    rejected[str(error)] += 1
                    continue
                valid += 1
                key = first.structure(candidate)
                if key in seen:
                    continue
                seen.add(key)
                price = first.price(candidate)
                receipts.append(compact_price(key, price))
                if price['ledger']['boot']['selected'] > ceiling:
                    continue
                step = {'pattern': pattern, 'rebound_transfer_occurrences': changed,
                        'structure_sha256': key, 'price': price}
                new_path = path + [step]
                if parent.score(price) < parent.score(selected):
                    selected, selected_path = price, new_path
                pool.append((candidate, new_path, price, key))
            if not exhausted:
                break
        complete_depths += exhausted
        pool.sort(key=lambda item: (parent.score(item[2]), item[3]))
        frontier = pool[:beam_width]
        report = {'depth': depth, 'tested': tested, 'valid': valid,
                  'distinct_complete_prices': len(receipts),
                  'frontier_candidates': len(pool), 'retained': len(frontier),
                  'selected_score': parent.score(selected), 'complete_depth': exhausted}
        depth_reports.append(report)
        print(json.dumps(report), flush=True)
        if selected['ledger']['boot']['selected'] <= 238:
            stopped = 'requested state target reached'
            break
        if not exhausted:
            stopped = 'candidate bound'
            break
        if not frontier:
            stopped = 'retained frontier exhausted'
            break
    inputs = first.input_hashes()
    inputs[str(parent.PLAN.relative_to(first.REPO))] = hashlib.sha256(parent.PLAN.read_bytes()).hexdigest()
    return {
        'format': 'context-rebound-paid-beam-v1', 'source_class': 'ReboundClean',
        'inputs': inputs, 'baseline_price': baseline, 'selected_price': selected,
        'accepted': selected_path, 'graph_sha256': p.gs.digest(original),
        'primitive_occurrences': len(original),
        'control_edges': sum(len(row) - 1 for row in original),
        'tested_candidates': tested, 'valid_candidates': valid,
        'distinct_complete_prices': receipts,
        'candidate_price_columns': ['structure_sha256', 'boot_raw', 'boot_quotient',
            'counted_raw', 'counted_quotient', 'grammar', 'runtime', 'max_zero_run'],
        'candidate_price_scope': 'All distinct tested grammars were completely compiled; compact counts retained.',
        'rejection_counts': dict(rejected), 'depth_reports': depth_reports,
        'complete_depths': complete_depths, 'max_depth': max_depth,
        'beam_width': beam_width, 'max_candidates': max_candidates,
        'temporary_state_allowance': allowance, 'stop_reason': stopped,
    }


class BeamGrammar(parent.ReboundClean):
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
    parser.add_argument('--max-depth', type=int, default=12)
    parser.add_argument('--beam-width', type=int, default=16)
    parser.add_argument('--max-candidates', type=int, default=30000)
    parser.add_argument('--allowance', type=int, default=1)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    if args.search:
        if PLAN.exists():
            raise ValueError('Refusing to overwrite a fixed plan')
        plan = search(args.max_depth, args.beam_width, args.max_candidates, args.allowance)
        PLAN.write_text(json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n')
        print(json.dumps({key: value for key, value in plan.items()
                          if key not in ('inputs', 'distinct_complete_prices', 'accepted', 'depth_reports')}, indent=2))
    if args.out:
        if args.out.exists():
            raise ValueError('Fresh output directory required')
        builder, ledger, _ = p.opt.compile_candidate(BeamGrammar, args.out)
        assert ledger == json.loads(PLAN.read_text())['selected_price']['ledger']
        (args.out / 'run-dispatch.json').write_text(json.dumps(builder.run_dispatch_certificate,
                                                            sort_keys=True, indent=2) + '\n')
        print(json.dumps(ledger, indent=2))
    elif not args.search:
        parser.error('--search or --out required')
