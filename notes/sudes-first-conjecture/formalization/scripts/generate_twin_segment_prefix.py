#!/usr/bin/env python3
"""Generate independent compressed twin-scan chunks with certified prefixes.

The pinned FT table supplies untrusted count hints. Each generated block checks
its hint with Lean's kernel and applies the prefix scanner theorem with an
explicit, kernel-checked padded-lookahead bound. No generated count is accepted
until the corresponding Lean target succeeds. This is a separate generator;
the existing full-base generator and already generated sources are unchanged.

Run with Python 3.12.13 (repository .python-version); the Lean toolchain is
leanprover/lean4:v4.33.1. Generation preflights all target paths but is not a
concurrency lock or atomic transaction; use a single writer. --output-dir is
available for validation outside the source tree.
"""
import argparse
import hashlib
import json
import types
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
INPUT = ROOT / 'problems/prime-line-sums/inputs/cutoff2_finite_twin_seed_inputs.json'
OUT = ROOT / 'formalizations/sude/Sude/GeneratedTwinScan'
BASE_GENERATOR = ROOT / 'formalizations/sude/scripts/generate_twin_segment.py'
INPUT_SHA256 = '7a060eccd40439f4c02bf423a7cc09ffb9a3b0cc1d488b5e288c62a287cecfd9'
GENERATOR_SHA256 = '2a3d0303a5647b1b8797735ad0dd21504cf4a1d4c6c8ba5e24185d75839ae19d'
LEAN_TOOLCHAIN = 'leanprover/lean4:v4.33.1'
PYTHON_CI_VERSION = '3.12.13'
BASE_LIMIT = 32768
BOUND = 2 ** 30
BLOCK = 16384
BLOCKS_PER_MODULE = 4


def read_pinned(path, expected):
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected:
        raise ValueError(f'source hash mismatch: {path}')
    return raw


def load_base_generator():
    raw = read_pinned(BASE_GENERATOR, GENERATOR_SHA256)
    module = types.ModuleType('pinned_twin_generator')
    module.__file__ = str(BASE_GENERATOR)
    exec(compile(raw, str(BASE_GENERATOR), 'exec'), module.__dict__)
    return module


def padded_lookahead(lo, hi):
    """Mirror the Lean stride-six alignment, with natural subtraction."""
    first = lo + (5 - lo % 6)
    width = (max(hi - first, 0) + 5) // 6
    return first + 2 * (3 * width + 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('segment', type=int)
    parser.add_argument('--output-dir', type=Path, default=OUT,
                        help='directory for generated Lean sources (pre-existing targets are rejected)')
    args = parser.parse_args()
    if (ROOT / 'formalizations/sude/lean-toolchain').read_text(encoding='utf-8').strip() != LEAN_TOOLCHAIN:
        raise ValueError('Lean toolchain pin differs')
    if (ROOT / '.python-version').read_text(encoding='utf-8').strip() != PYTHON_CI_VERSION:
        raise ValueError('CI Python version pin differs')
    data = json.loads(read_pinned(INPUT, INPUT_SHA256))
    rows = data['segments']
    if len(rows) != 512 or not 0 <= args.segment < len(rows):
        raise ValueError('invalid source segment')
    base = load_base_generator()
    row = rows[args.segment]
    lo = row['lo']
    stop = min(row['hi'] + 2, BOUND - 1)
    if lo < 5 or lo % 2 != 1 or stop < lo or (stop - lo) % 2:
        raise ValueError('invalid odd segment geometry')
    width = (stop - lo) // 2
    mask = base.mask_segment(lo, width, base.prime_base(isqrt(BOUND)))
    blocks = []
    for offset in range(0, width, BLOCK):
        size = min(BLOCK, width - offset)
        block_lo = lo + 2 * offset
        hi = block_lo + 2 * size
        lookahead = padded_lookahead(block_lo, hi)
        bound = isqrt(lookahead)
        if bound > BASE_LIMIT or lookahead >= (bound + 1) ** 2:
            raise ValueError('padded lookahead exceeds certified base')
        count = mask[offset:offset + size + 1].count(b'\x01\x01')
        blocks.append((block_lo, hi, bound, count))
    if not blocks:
        raise ValueError('empty segment has no generated aggregate')
    expected = row['pairs_internal'] + (rows[args.segment + 1]['pairs_crossing']
                                        if args.segment + 1 < len(rows) else 0)
    if sum(count for _, _, _, count in blocks) != expected:
        raise ValueError('hint total differs from source table boundary convention')
    namespace = f'S{args.segment:03}'
    chunk_count = (len(blocks) + BLOCKS_PER_MODULE - 1) // BLOCKS_PER_MODULE
    targets = [args.output_dir / f'{namespace}C{i:02}.lean' for i in range(chunk_count)]
    targets.append(args.output_dir / f'{namespace}All.lean')
    existing = [path for path in targets if path.exists() or path.is_symlink()]
    if existing:
        raise FileExistsError(f'output target already exists: {existing[0]}')
    args.output_dir.mkdir(parents=True, exist_ok=True)
    module_spans = []
    for start in range(0, len(blocks), BLOCKS_PER_MODULE):
        idx = start // BLOCKS_PER_MODULE
        mod = f'{namespace}C{idx:02}'
        lines = ['import Sude.FiniteTwinTakeWhileBase', 'import Sude.FiniteTwinActive', '',
                 '/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/',
                 'namespace Sude.GeneratedTwinScan', f'namespace {mod}',
                 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '']
        spans = []
        for j, (block_lo, hi, bound, count) in enumerate(blocks[start:start + BLOCKS_PER_MODULE]):
            prefix = f'(finiteTwinCheckedBase.takeWhile (fun p => p ≤ {bound}))'
            lines += [f'theorem checked{j} : strideSixCompressedIntervalScan {prefix} {block_lo} {hi} = {count} := by',
                      '  decide +kernel', '',
                      f'theorem block{j} : (twinPrimeSegment {block_lo} {hi}).card = {count} := by',
                      f'  have h := finiteTwinTakeWhile_compressed_interval_spec {bound} {block_lo} {hi}',
                      '    (by decide) (by decide) (by decide)',
                      f'  rw [checked{j}] at h', '  exact h.symm', '']
            spans.append((block_lo, hi, count, f'block{j}'))
        first, last, total, proof = base.combine_tree(lines, spans, 'join')
        lines += [f'theorem total : (twinPrimeSegment {first} {last}).card = {total} := {proof}', '',
                  f'end {mod}', 'end Sude.GeneratedTwinScan']
        targets[idx].write_text('\n'.join(lines) + '\n', encoding='utf-8', newline='\n')
        module_spans.append((first, last, total, f'{mod}.total'))
    imports = [f'import Sude.GeneratedTwinScan.{namespace}C{i:02}' for i in range(chunk_count)]
    lines = imports + ['', '/-! Combined FT source segment; Lean kernel check required. -/',
             'namespace Sude.GeneratedTwinScan', f'namespace {namespace}All', '']
    first, last, total, proof = base.combine_tree(lines, module_spans, 'join')
    lines += [f'theorem total : (twinPrimeSegment {first} {last}).card = {total} := {proof}', '',
              f'end {namespace}All', 'end Sude.GeneratedTwinScan']
    targets[-1].write_text('\n'.join(lines) + '\n', encoding='utf-8', newline='\n')
    print(f'{namespace}: {len(blocks)} blocks, {chunk_count} modules, untrusted count hints total {total}')


if __name__ == '__main__':
    main()
