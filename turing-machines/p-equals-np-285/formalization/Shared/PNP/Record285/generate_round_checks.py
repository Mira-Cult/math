"""Generate bounded kernel checks for the proposed initialization cycles.

The generator supplies proof tasks only. Lean independently checks each
four-cycle Boolean certificate against the exact physical command checker.
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent
BLOCK_SIZE = 4
BLOCKS_PER_SHARD = 119
for shard in range(4):
    start = 2 + shard * BLOCK_SIZE * BLOCKS_PER_SHARD
    out = [
        'import Shared.PNP.Record285.InitializationRounds', '',
        '/-! Generated bounded checks for actual literal-machine cycles. -/',
        'set_option maxRecDepth 16384', 'set_option maxHeartbeats 0',
        'set_option exponentiation.threshold 8192',
        f'namespace Shared.PNP.Record285.InitializationRoundCheck{shard}',
        'open Shared.PNP.Record285.InitializationRounds', '',
    ]
    for i in range(BLOCKS_PER_SHARD):
        n = start + BLOCK_SIZE * i
        out.append(f'theorem block{i} : (List.range\' {n} {BLOCK_SIZE}).all checkRound = true := by decide')
    last = BLOCKS_PER_SHARD - 1
    n = start + BLOCK_SIZE * last
    out += ['', f'theorem suffix{last} : (List.range\' {n} {BLOCK_SIZE}).all checkRound = true := block{last}']
    for i in range(last-1, -1, -1):
        n = start + BLOCK_SIZE * i
        rest = BLOCK_SIZE * (last-i)
        out.append(f'theorem suffix{i} : (List.range\' {n} {BLOCK_SIZE+rest}).all checkRound = true := '
                   f'range_join {n} {BLOCK_SIZE} {rest} block{i} suffix{i+1}')
    out += ['', f'theorem checked : (List.range\' {start} {BLOCK_SIZE*BLOCKS_PER_SHARD}).all checkRound = true := suffix0', '',
            f'end Shared.PNP.Record285.InitializationRoundCheck{shard}']
    (HERE / f'InitializationRoundCheck{shard}.lean').write_text('\n'.join(out)+'\n', encoding='utf-8')
print('1904 cycles in four independently checkable shards')
