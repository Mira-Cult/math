#!/usr/bin/env python3
"""Generate the final FT composition after all 512 Lean segments are checked.

The source table only supplies untrusted count hints. Importing the generated
module requires every segment theorem to be kernel-checked first.
"""
import hashlib
import json
from pathlib import Path
from generate_twin_segment import INPUT, OUT, SHA256, BOUND, combine_tree


def main():
    raw = INPUT.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SHA256:
        raise ValueError('FT source input hash mismatch')
    rows = json.loads(raw)['segments']
    if len(rows) != 512:
        raise ValueError('incorrect segment count')
    spans = []
    for i, row in enumerate(rows):
        lo = row['lo']
        stop = min(row['hi'] + 2, BOUND - 1)
        count = row['pairs_internal'] + (rows[i + 1]['pairs_crossing'] if i + 1 < len(rows) else 0)
        if spans and spans[-1][1] != lo:
            raise ValueError('noncontiguous source segments')
        spans.append((lo, stop, count, f'S{i:03}All.total'))
    if spans[0][0] != 45 or spans[-1][1] != BOUND - 1 or sum(s[2] for s in spans) != 3650551:
        raise ValueError('unexpected source range or total')
    OUT.mkdir(parents=True, exist_ok=True)
    lines = [f'import Sude.GeneratedTwinScan.S{i:03}All' for i in range(len(rows))]
    lines += ['', '/-! Final FT composition: all imported segment claims must be checked. -/',
              'namespace Sude.GeneratedTwinScan', 'namespace All', '']
    lo, hi, count, proof = combine_tree(lines, spans, 'join')
    lines += [f'theorem total : (twinPrimeSegment {lo} {hi}).card = {count} := {proof}', '',
              'theorem finiteTwinSeeds_card : finiteTwinSeeds.card = 3650551 := by',
              '  simpa [finiteTwinSeeds] using total', '', 'end All', 'end Sude.GeneratedTwinScan']
    (OUT / 'All.lean').write_text('\n'.join(lines) + '\n')
    print('Generated FT aggregation; it is not proved until all 512 imports and this module build.')


if __name__ == '__main__':
    main()
