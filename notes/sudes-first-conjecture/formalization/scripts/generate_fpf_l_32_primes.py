#!/usr/bin/env python3
"""Generate stage-split Lucas certificates for the first 32 L pairs per stage.

Lean checks every certificate and its association with the already checked
L32Distinct endpoints. This does not certify the entire FPF population.
"""
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
OUT = ROOT / 'formalizations/sude/Sude/GeneratedPrefix/L32Primes'
MANIFEST_SHA = 'bbb0f738d6ee37c82170727c88912b5c74010b053aed19f799df80eef5badcee'
CPP_SHA = '9deb0fa9a0f598fbc8db8f0fde415ac0fc9959c21141cac96ad8433327d61e76'


def write(path, text):
    if not path.exists() or path.read_text() != text:
        path.write_text(text)


def main():
    raw = MANIFEST.read_bytes()
    if hashlib.sha256(raw).hexdigest() != MANIFEST_SHA or hashlib.sha256(CPP.read_bytes()).hexdigest() != CPP_SHA:
        raise ValueError('frozen FPF source digest mismatch')
    profile = json.loads(raw)['profiles'][0]
    if (profile['name'], profile['stages'], profile['pairs_per_stage']) != ('L', 24, 14448):
        raise ValueError('unexpected L profile')
    compiler = shutil.which('clang++') or shutil.which('g++')
    if compiler is None:
        raise ValueError('a C++17 compiler is required')
    with tempfile.TemporaryDirectory(prefix='sude-fpf-l32-primes-') as tmp:
        binary, stem = Path(tmp) / 'generator', Path(tmp) / 'population'
        subprocess.run([compiler, '-O3', '-std=c++17', str(CPP), '-o', str(binary)], check=True)
        subprocess.run([str(binary), str(stem), '60000000', '14448', '24', '13000000', '55000000'],
                       check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stream = stem.with_suffix('.bin').read_bytes()
    if hashlib.sha256(stream).hexdigest() != profile['stream_sha256'] or len(stream) != 4 * 24 * 14448:
        raise ValueError('reproduced stream digest or length mismatch')
    source = struct.unpack('<' + str(len(stream) // 4) + 'I', stream)
    lows = [source[j * 14448:j * 14448 + 32] for j in range(24)]
    if any(row[0] != profile['rows'][j]['first_lower'] for j, row in enumerate(lows)):
        raise ValueError('stream and source rows disagree')
    spec = importlib.util.spec_from_file_location('first_tail_generator', HELPER)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    OUT.mkdir(parents=True, exist_ok=True)
    total = 0
    for j, row in enumerate(lows):
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

        for low in row:
            add(low)
            add(low + 2 ** (j + 1))
        total += len(nodes)
        entries = []
        for value, (a, factors) in sorted(nodes.items()):
            fs = ', '.join(f'({q}, {e})' for q, e in factors)
            entries.append(f'  ⟨{value}, {a}, [{fs}]⟩')
        imports = ['import Sude.LucasCertificate', 'import Sude.GeneratedPrefix.L32Distinct.All']
        if j:
            imports.append(f'import Sude.GeneratedPrefix.L32Primes.Stage{j - 1:02d}')
        lines = imports + ['', f'namespace Sude.GeneratedPrefix.L32Primes.Stage{j:02d}',
            'open Sude.GeneratedPrefix.L32Distinct',
            'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '',
            'def nodes : List Lucas.Node := [', ',\n'.join(entries), ']', '',
            'theorem nodes_checked : Lucas.checkCertificate nodes = true := by decide +kernel', '',
            'theorem endpoints_in_nodes :',
            f'    ∀ (i : Fin 32) (side : Bool), endpoint ((({j} : Fin 24), i), side) ∈ nodes.map Lucas.Node.value := by',
            '  decide +kernel', '',
            'theorem prime (i : Fin 32) (side : Bool) :',
            f'    Nat.Prime (endpoint ((({j} : Fin 24), i), side)) := by',
            '  obtain ⟨node, hnode, heq⟩ := List.mem_map.mp (endpoints_in_nodes i side)',
            '  rw [← heq]',
            '  exact Lucas.checkCertificate_sound nodes nodes_checked node hnode', '',
            f'end Sude.GeneratedPrefix.L32Primes.Stage{j:02d}', '',
        ]
        write(OUT / f'Stage{j:02d}.lean', '\n'.join(lines))
    all_lines = ['import Sude.GeneratedPrefix.L32Primes.Stage23',
        'import Sude.FinitePrefixPoolBound', '',
        '/-! Primality for a source slice only; complete FPF acceptance remains open. -/',
        'namespace Sude.GeneratedPrefix.L32Primes',
        'open Sude.GeneratedPrefix.L32Distinct',
        'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '',
        'theorem endpoint_prime (x : (Fin 24 × Fin 32) × Bool) : Nat.Prime (endpoint x) := by',
        '  rcases x with ⟨⟨j, i⟩, side⟩', '  fin_cases j']
    all_lines += [f'  · exact Stage{j:02d}.prime i side' for j in range(24)]
    all_lines += ['', 'theorem endpoint_bounds : ∀ x, endpoint x ≠ 2 ∧ endpoint x ≤ 55000000 := by',
        '  decide +kernel', '',
        'theorem endpoint_in_pool (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)',
        '    (x : (Fin 24 × Fin 32) × Bool) : endpoint x ∈ pool n := by',
        '  have hb := endpoint_bounds x',
        '  exact finitePrefix_L_prime_in_pool lower hn (endpoint_prime x) hb.1 (by omega)', '',
        'def poolValues (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :',
        '    (Fin 24 × Fin 32) × Bool → pool n := fun x => ⟨endpoint x, endpoint_in_pool lower hn x⟩', '',
        'theorem poolValues_injective (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :',
        '    Function.Injective (poolValues lower hn) := by',
        '  intro x y h', '  exact endpoint_injective (congrArg Subtype.val h)', '',
        'theorem poolValues_gap (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n)',
        '    (j : Fin 24) (i : Fin 32) :',
        '    (poolValues lower hn ((j, i), true)).val =',
        '      (poolValues lower hn ((j, i), false)).val + 2 ^ (j.val + 1) := by',
        '  simp [poolValues, endpoint]', '', 'end Sude.GeneratedPrefix.L32Primes', '']
    write(OUT / 'All.lean', '\n'.join(all_lines))
    print(f'24 source stages, 768 pairs, 1536 endpoints, {total} stage-local Lucas nodes')


if __name__ == '__main__':
    main()
