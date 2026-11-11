#!/usr/bin/env python3
"""Generate one L-family stage's prime-pair blocks from the pinned source stream.

Every selected endpoint and range check is rechecked by Lean. --chunks controls
how many consecutive 32-pair blocks are generated; the full stage needs 452.
Partial generation does not claim the complete stage or controller.
"""
import argparse
import hashlib
import importlib.util
import json
import shutil
import struct
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MANIFEST = ROOT / 'problems/prime-line-sums/inputs/cutoff2_finite_prefix_family_inputs.json'
CPP = ROOT / 'problems/prime-line-sums/code/cutoff2_finite_prefix_family_generator.cpp'
HELPER = Path(__file__).with_name('generate_first_tail_segment.py')
OUT_ROOT = ROOT / 'formalizations/sude/Sude/GeneratedPrefix'
MANIFEST_SHA = 'bbb0f738d6ee37c82170727c88912b5c74010b053aed19f799df80eef5badcee'
CPP_SHA = '9deb0fa9a0f598fbc8db8f0fde415ac0fc9959c21141cac96ad8433327d61e76'
QMAX, SIZE = 14448, 32
MAX_CHUNKS = (QMAX + SIZE - 1) // SIZE


def write(path, text):
    if not path.exists() or path.read_text() != text:
        path.write_text(text)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--stage', type=int, default=0)
    parser.add_argument('--chunks', type=int, default=MAX_CHUNKS)
    parser.add_argument('--full-target', action='store_true',
                        help='write AllFull.lean instead of the current All.lean checkpoint')
    args = parser.parse_args()
    if not 0 <= args.stage < 24:
        raise ValueError('--stage must be in 0..23')
    if not 1 <= args.chunks <= MAX_CHUNKS:
        raise ValueError(f'--chunks must be in 1..{MAX_CHUNKS}')
    raw = MANIFEST.read_bytes()
    if hashlib.sha256(raw).hexdigest() != MANIFEST_SHA or hashlib.sha256(CPP.read_bytes()).hexdigest() != CPP_SHA:
        raise ValueError('frozen FPF source digest mismatch')
    profile = json.loads(raw)['profiles'][0]
    if (profile['name'], profile['stages'], profile['pairs_per_stage']) != ('L', 24, QMAX):
        raise ValueError('unexpected L profile')
    compiler = shutil.which('clang++') or shutil.which('g++')
    if compiler is None:
        raise ValueError('a C++17 compiler is required')
    with tempfile.TemporaryDirectory(prefix=f'sude-fpf-stage{args.stage}-') as tmp:
        binary, stem = Path(tmp) / 'generator', Path(tmp) / 'population'
        subprocess.run([compiler, '-O3', '-std=c++17', str(CPP), '-o', str(binary)], check=True)
        subprocess.run([str(binary), str(stem), '60000000', str(QMAX), '24', '13000000', '55000000'],
                       check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stream = stem.with_suffix('.bin').read_bytes()
    if hashlib.sha256(stream).hexdigest() != profile['stream_sha256'] or len(stream) != 4 * 24 * QMAX:
        raise ValueError('reproduced stream digest or length mismatch')
    source = struct.unpack('<' + str(len(stream) // 4) + 'I', stream)
    lows = source[args.stage * QMAX:(args.stage + 1) * QMAX]
    row = profile['rows'][args.stage]
    gap = 2 ** (args.stage + 1)
    if row['stage'] != args.stage or row['gap'] != gap:
        raise ValueError('source stage index or gap mismatch')
    if lows[0] != row['first_lower'] or lows[-1] != row['last_lower']:
        raise ValueError('stage endpoints disagree with the source manifest')
    if any(a >= b for a, b in zip(lows, lows[1:])):
        raise ValueError('source stage is not strictly increasing')
    spec = importlib.util.spec_from_file_location('first_tail_generator', HELPER)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    out = OUT_ROOT / f'LStage{args.stage}'
    module = f'Sude.GeneratedPrefix.LStage{args.stage}'
    out.mkdir(parents=True, exist_ok=True)
    total_nodes = 0
    for j in range(args.chunks):
        selected = lows[j * SIZE:min((j + 1) * SIZE, QMAX)]
        nodes = {}

        def add(value):
            if value in nodes:
                return
            if value == 2:
                nodes[value] = (1, [])
                return
            factors = helper.factor(value - 1)
            for q, _ in factors:
                add(q)
            nodes[value] = (helper.witness(value, factors), factors)

        for low in selected:
            add(low)
            add(low + gap)
        total_nodes += len(nodes)
        entries = []
        for value, (a, factors) in sorted(nodes.items()):
            fs = ', '.join(f'({q}, {e})' for q, e in factors)
            entries.append(f'  ⟨{value}, {a}, [{fs}]⟩')
        imports = ['import Sude.PrefixStageCertificate']
        if j:
            imports.append(f'import {module}.B{j - 1:03d}')
        ns = f'{module}.B{j:03d}'
        lines = imports + ['', f'namespace {ns}',
            'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '',
            'def nodes : List Lucas.Node := [', ',\n'.join(entries), ']', '',
            'def lows : List ℕ := [' + ', '.join(map(str, selected)) + ']', '',
            'theorem nodes_checked : Lucas.checkCertificate nodes = true := by decide +kernel', '',
            f'theorem data_checked : PrefixStageBlockData nodes {gap} 55000000 {selected[0]} {selected[-1]} lows := by',
            '  decide +kernel', '',
            f'theorem block_valid : PrefixStageBlock {gap} 55000000 {selected[0]} {selected[-1]} lows :=',
            f'  prefixStageBlock_of_certificate nodes {gap} 55000000 {selected[0]} {selected[-1]} lows',
            '    nodes_checked data_checked', '']
        if j == 0:
            lines += ['def accumulated : List ℕ := lows', '',
                f'theorem prefix_valid : PrefixStageBlock {gap} 55000000 {lows[0]} {selected[-1]} accumulated := block_valid', '',
                f'theorem prefix_length : accumulated.length = {len(selected)} := by decide +kernel', '']
        else:
            prev = f'B{j - 1:03d}'
            count = min((j + 1) * SIZE, QMAX)
            lines += [f'def accumulated : List ℕ := {prev}.accumulated ++ lows', '',
                f'theorem prefix_valid : PrefixStageBlock {gap} 55000000 {lows[0]} {selected[-1]} accumulated := by',
                f'  exact PrefixStageBlock.append {prev}.prefix_valid block_valid (by decide) (by decide) (by decide)', '',
                f'theorem prefix_length : accumulated.length = {count} := by',
                f'  simp [accumulated, {prev}.prefix_length, lows]', '']
        lines += [f'end {ns}', '']
        write(out / f'B{j:03d}.lean', '\n'.join(lines))
    last = args.chunks - 1
    count = min(args.chunks * SIZE, QMAX)
    name = f'B{last:03d}'
    lines = [f'import {module}.{name}', '',
        f'/-! Checked stage-{args.stage} prefix. Full acceptance requires all 452 blocks. -/',
        f'namespace {module}',
        'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '',
        f'abbrev lows : List ℕ := {name}.accumulated', '',
        f'theorem length : lows.length = {count} := {name}.prefix_length', '',
        f'theorem valid : PrefixStageBlock {gap} 55000000 {lows[0]} {lows[count - 1]} lows := {name}.prefix_valid', '',
        'theorem pool_matching (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :',
        f'    (∀ p ∈ lows.toFinset, p ∈ pool n ∧ p + {gap} ∈ pool n) ∧',
        f'      PairwiseDisjointPairs lows.toFinset {gap} ∧',
        f'      (pairFootprint lows.toFinset {gap}).card = 2 * {count} := by',
        f'  have h := PrefixStageBlock.L_pool_matching (j := {args.stage}) lower hn (by decide) {name}.prefix_valid',
        '  simpa [lows, length] using h', '',
        f'end {module}', '']
    write(out / ('AllFull.lean' if args.full_target else 'All.lean'), '\n'.join(lines))
    print(f'stage {args.stage}: {args.chunks}/{MAX_CHUNKS} blocks, {count}/{QMAX} pairs, {total_nodes} local Lucas nodes')


if __name__ == '__main__':
    main()
