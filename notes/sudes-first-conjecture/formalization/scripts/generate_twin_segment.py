#!/usr/bin/env python3
"""Generate Lean-checkable FT segment certificates from untrusted sieve hints.

Each generated numerical claim is independently checked by Lean's kernel.
The input hash pins the source segment geometry and review table; comparing
counts here is a generation check, not a mathematical proof.

Use `--independent-chunks` to remove the serial imports between chunks and
make the segment aggregate import each chunk directly. This changes only the
import graph; every generated count still requires a Lean kernel build. Use
`--geometric-scan` to generate numerical certificates with the alternative
verified geometric-mask scanner, or `--compressed-scan` with
`--independent-chunks` for the compressed stride-six scanner. The default
scanner is unchanged. Generation
preflights for existing outputs; use a single writer because this is not a
concurrency lock or an atomic transaction. Use
`--output-dir PATH` to inspect generated files outside the default directory.
"""
import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
INPUT = ROOT / 'problems/prime-line-sums/inputs/cutoff2_finite_twin_seed_inputs.json'
OUT = ROOT / 'formalizations/sude/Sude/GeneratedTwinScan'
SHA256 = '7a060eccd40439f4c02bf423a7cc09ffb9a3b0cc1d488b5e288c62a287cecfd9'
BOUND = 2 ** 30
BLOCK = 16384
SUB = 4096
BLOCKS_PER_MODULE = 4


def prime_base(limit):
    flags = bytearray(b'\x01') * (limit + 1)
    flags[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p * p::p] = b'\x00' * ((limit - p * p) // p + 1)
    return [p for p in range(3, limit + 1, 2) if flags[p]]


def mask_segment(lo, width, primes):
    hi = lo + 2 * width  # inclusive lookahead candidate
    mask = bytearray(b'\x01') * (width + 1)
    for p in primes:
        if p * p > hi:
            break
        start = max(p * p, ((lo + p - 1) // p) * p)
        if start % 2 == 0:
            start += p
        if start <= hi:
            index = (start - lo) // 2
            mask[index::p] = b'\x00' * ((width - index) // p + 1)
    if b'\x01\x01\x01' in mask:
        raise ValueError('unexpected overlapping pair hints')
    return mask


def combine_tree(lines, spans, prefix):
    level = 0
    while len(spans) > 1:
        merged = []
        for i in range(0, len(spans), 2):
            if i + 1 == len(spans):
                merged.append(spans[i])
                continue
            lo, mid, a, left = spans[i]
            mid2, hi, b, right = spans[i + 1]
            if mid != mid2:
                raise ValueError('noncontiguous blocks')
            name = f'{prefix}_{level}_{i // 2}'
            lines += [f'theorem {name} : (twinPrimeSegment {lo} {hi}).card = {a+b} := by',
                      f'  simpa using combineTwinPrimeSegments (by decide : {lo} ≤ {mid})',
                      f'    (by decide : {mid} ≤ {hi}) {left} {right}', '']
            merged.append((lo, hi, a + b, name))
        spans = merged
        level += 1
    return spans[0]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('segment', type=int)
    parser.add_argument('--independent-chunks', action='store_true',
                        help='make chunks independent; preflight existing targets (single writer only)')
    scanner = parser.add_mutually_exclusive_group()
    scanner.add_argument('--geometric-scan', action='store_true',
                         help='use the proved geometric-mask scanner for new generated blocks')
    scanner.add_argument('--compressed-scan', action='store_true',
                         help='use the proved compressed stride-six scanner (requires independent chunks)')
    parser.add_argument('--output-dir', type=Path, default=OUT,
                        help='directory for generated Lean files (default: Sude/GeneratedTwinScan)')
    args = parser.parse_args()
    if args.compressed_scan and not args.independent_chunks:
        parser.error('--compressed-scan requires --independent-chunks')
    raw = INPUT.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SHA256:
        raise ValueError('FT source input hash mismatch')
    data = json.loads(raw)
    rows = data['segments']
    if len(rows) != 512 or not 0 <= args.segment < len(rows):
        raise ValueError('invalid source segment')
    row = rows[args.segment]
    lo = row['lo']
    stop = min(row['hi'] + 2, BOUND - 1)
    if lo % 2 != 1 or (stop - lo) % 2:
        raise ValueError('invalid odd segment geometry')
    width = (stop - lo) // 2
    mask = mask_segment(lo, width, prime_base(isqrt(BOUND)))
    blocks = []
    for offset in range(0, width, BLOCK):
        size = min(BLOCK, width - offset)
        window = mask[offset:offset + size + 1]
        count = window.count(b'\x01\x01')
        blocks.append((lo + 2 * offset, size, count))
    expected = row['pairs_internal'] + (rows[args.segment + 1]['pairs_crossing'] if args.segment + 1 < len(rows) else 0)
    if sum(b[2] for b in blocks) != expected:
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
        chunk = blocks[start:start + BLOCKS_PER_MODULE]
        idx = start // BLOCKS_PER_MODULE
        mod = f'{namespace}C{idx:02}'
        deps = ['import Sude.FiniteTwinOddBaseComplete', 'import Sude.FiniteTwinActive']
        if args.geometric_scan:
            deps.append('import Sude.TwinGeometricScan')
        if args.compressed_scan:
            deps.append('import Sude.TwinStrideSixCompressed')
        if idx and not args.independent_chunks:
            deps.append(f'import Sude.GeneratedTwinScan.{namespace}C{idx - 1:02}')
        if args.segment == 0 and idx == 0 and not args.geometric_scan and not args.compressed_scan:
            deps.append('import Sude.FiniteTwinLowActive65536')
        lines = deps + ['', '/-! Generated FT count hints; Lean checks each block. -/',
                        'namespace Sude.GeneratedTwinScan', f'namespace {mod}',
                        'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '']
        spans = []
        for j, (block_lo, size, count) in enumerate(chunk):
            hi = block_lo + 2 * size
            name = f'block{j}'
            if args.segment == 0 and idx == 0 and not args.geometric_scan and not args.compressed_scan:
                lines += [f'theorem {name} : (twinPrimeSegment {block_lo} {hi}).card = {count} :=',
                          f'  finiteTwinLowBlock{j}_mathematical', '']
            else:
                widths = [SUB] * (size // SUB)
                if size % SUB:
                    widths.append(size % SUB)
                ws = '[' + ', '.join(map(str, widths)) + ']'
                if args.compressed_scan:
                    lines += [f'theorem checked{j} : strideSixCompressedIntervalScan finiteTwinCheckedBase {block_lo} {hi} = {count} := by',
                              '  decide +kernel', '',
                              f'theorem {name} : (twinPrimeSegment {block_lo} {hi}).card = {count} := by',
                              f'  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 {block_lo} {hi}',
                              '    finiteTwinCheckedBase_complete (by decide) (by decide)',
                              f'  rw [checked{j}] at h', '  exact h.symm', '']
                elif args.geometric_scan:
                    lines += [f'def widths{j} : List ℕ := {ws}', '',
                              f'theorem checked{j} : geometricActiveStreamingTwinScan finiteTwinCheckedBase {block_lo} widths{j} = {count} := by',
                              '  decide +kernel', '',
                              f'theorem {name} : (twinPrimeSegment {block_lo} {hi}).card = {count} := by',
                              f'  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 {block_lo} widths{j}',
                              '    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)',
                              f'  rw [checked{j}] at h', f'  simpa [widths{j}] using h.symm', '']
                else:
                    lines += [f'def widths{j} : List ℕ := {ws}', '',
                              f'theorem checked{j} : activeStreamingTwinScan finiteTwinCheckedBase {block_lo} widths{j} = {count} := by',
                              '  decide +kernel', '',
                              f'theorem {name} : (twinPrimeSegment {block_lo} {hi}).card = {count} := by',
                              f'  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase {block_lo} widths{j}).symm.trans checked{j}',
                              f'  have hb := (streamingTwinScan_eq finiteTwinCheckedBase {block_lo} widths{j}).symm.trans hs',
                              f'  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 {block_lo} widths{j}',
                              '    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)',
                              '  rw [hb] at h', f'  simpa [widths{j}] using h.symm', '']
            spans.append((block_lo, hi, count, name))
        first, last, total, proof = combine_tree(lines, spans, 'join')
        lines += [f'theorem total : (twinPrimeSegment {first} {last}).card = {total} := {proof}', '',
                  f'end {mod}', 'end Sude.GeneratedTwinScan']
        (args.output_dir / f'{mod}.lean').write_text('\n'.join(lines) + '\n')
        module_spans.append((first, last, total, f'{mod}.total'))
    allmod = f'{namespace}All'
    if args.independent_chunks:
        imports = [f'import Sude.GeneratedTwinScan.{namespace}C{i:02}'
                   for i in range(len(module_spans))]
    else:
        imports = [f'import Sude.GeneratedTwinScan.{namespace}C{len(module_spans)-1:02}']
    header = '/-! Combined FT source segment; Lean kernel check required. -/'
    lines = imports + ['',
             header,
             'namespace Sude.GeneratedTwinScan', f'namespace {allmod}', '']
    first, last, total, proof = combine_tree(lines, module_spans, 'join')
    lines += [f'theorem total : (twinPrimeSegment {first} {last}).card = {total} := {proof}', '',
              f'end {allmod}', 'end Sude.GeneratedTwinScan']
    (args.output_dir / f'{allmod}.lean').write_text('\n'.join(lines) + '\n')
    print(f'{namespace}: {len(blocks)} blocks, {len(module_spans)} modules, untrusted count hints total {total}')


if __name__ == '__main__':
    main()
