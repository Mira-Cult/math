#!/usr/bin/env python3
"""Generate untrusted Lucas evidence for the first two L pairs at each stage.

This small fixture is not a certificate of the full FPF population. The
manifest supplies the values; Lean checks primality, gaps and distinctness.
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
EXPECTED_SHA256 = 'bbb0f738d6ee37c82170727c88912b5c74010b053aed19f799df80eef5badcee'
OUT = ROOT / 'formalizations/sude/Sude/GeneratedPrefix/FirstFamilyPairs.lean'
HELPER = Path(__file__).with_name('generate_first_tail_segment.py')
CPP = ROOT / 'problems/prime-line-sums/code/cutoff2_finite_prefix_family_generator.cpp'
CPP_SHA256 = '9deb0fa9a0f598fbc8db8f0fde415ac0fc9959c21141cac96ad8433327d61e76'


def main():
    raw = MANIFEST.read_bytes()
    if hashlib.sha256(raw).hexdigest() != EXPECTED_SHA256:
        raise ValueError('frozen FPF manifest digest mismatch')
    data = json.loads(raw)
    profile = data['profiles'][0]
    if (profile['name'], profile['stages'], profile['pairs_per_stage']) != ('L', 24, 14448):
        raise ValueError('unexpected L profile')
    rows = profile['rows']
    if len(rows) != 24 or any(row['stage'] != j or row['gap'] != 2 ** (j + 1)
                              for j, row in enumerate(rows)):
        raise ValueError('unexpected FPF stage sequence')
    if hashlib.sha256(CPP.read_bytes()).hexdigest() != CPP_SHA256:
        raise ValueError('frozen FPF generator digest mismatch')
    compiler = shutil.which('clang++') or shutil.which('g++')
    if compiler is None:
        raise ValueError('a C++17 compiler is required to reproduce the source stream')
    with tempfile.TemporaryDirectory(prefix='sude-fpf-l-') as tmp:
        binary = Path(tmp) / 'generator'
        stem = Path(tmp) / 'population'
        subprocess.run([compiler, '-O3', '-std=c++17', str(CPP), '-o', str(binary)], check=True)
        subprocess.run([str(binary), str(stem), '60000000', '14448', '24', '13000000', '55000000'],
                       check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stream = stem.with_suffix('.bin').read_bytes()
        if hashlib.sha256(stream).hexdigest() != profile['stream_sha256']:
            raise ValueError('reproduced L source stream digest mismatch')
    source = struct.unpack('<' + str(len(stream) // 4) + 'I', stream)
    if len(source) != 24 * 14448:
        raise ValueError('unexpected L source stream length')
    lows = [source[j * 14448:j * 14448 + 2] for j in range(24)]
    if any(low[0] != rows[j]['first_lower'] for j, low in enumerate(lows)):
        raise ValueError('stream and stage manifest disagree')
    endpoints = [p for j, row in enumerate(lows) for low in row
                 for p in (low, low + 2 ** (j + 1))]
    if len(set(endpoints)) != 96 or max(endpoints) > 55000000:
        raise ValueError('fixture endpoints are not distinct or exceed the source bound')
    spec = importlib.util.spec_from_file_location('first_tail_generator', HELPER)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    nodes = {}

    def add_node(value):
        if value in nodes:
            return
        if value == 2:
            nodes[value] = (1, [])
            return
        factors = helper.factor(value - 1)
        for q, _ in factors:
            add_node(q)
        nodes[value] = (helper.witness(value, factors), factors)

    for value in endpoints:
        add_node(value)
    encoded = []
    for value, (a, factors) in sorted(nodes.items()):
        fs = ', '.join(f'({q}, {e})' for q, e in factors)
        encoded.append(f'  ⟨{value}, {a}, [{fs}]⟩')
    lines = [
        'import Sude.LucasCertificate',
        'import Sude.FinitePrefixPoolBound', '',
        '/-! First two retained pairs from each L-family stage. The stream supplies',
        'the data; Lean checks the Lucas nodes and the finite pair properties.',
        'This is not a certificate of the complete FPF population. -/',
        'namespace Sude.GeneratedPrefix',
        'set_option maxRecDepth 100000',
        'set_option maxHeartbeats 0', '',
        'def firstFamilyNodes : List Lucas.Node := [',
        ',\n'.join(encoded), ']', '',
        'def firstFamilyLows : Fin 24 → Fin 2 → ℕ := ![' +
            ', '.join('![' + ', '.join(map(str, row)) + ']' for row in lows) + ']', '',
        'def firstFamilyEndpoint (x : (Fin 24 × Fin 2) × Bool) : ℕ :=',
        '  firstFamilyLows x.1.1 x.1.2 + if x.2 then 2 ^ (x.1.1.val + 1) else 0', '',
        'theorem firstFamilyNodes_checked : Lucas.checkCertificate firstFamilyNodes = true := by',
        '  decide +kernel', '',
        'theorem firstFamilyEndpoints_in_nodes :',
        '    ∀ x, firstFamilyEndpoint x ∈ firstFamilyNodes.map Lucas.Node.value := by',
        '  decide +kernel', '',
        'theorem firstFamilyEndpoint_injective : Function.Injective firstFamilyEndpoint := by',
        '  decide +kernel', '',
        'theorem firstFamilyEndpoint_bounds :',
        '    ∀ x, firstFamilyEndpoint x ≠ 2 ∧ firstFamilyEndpoint x ≤ 55000000 := by',
        '  decide +kernel', '',
        'theorem firstFamilyEndpoint_prime (x : (Fin 24 × Fin 2) × Bool) :',
        '    Nat.Prime (firstFamilyEndpoint x) := by',
        '  obtain ⟨node, hnode, heq⟩ := List.mem_map.mp (firstFamilyEndpoints_in_nodes x)',
        '  rw [← heq]',
        '  exact Lucas.checkCertificate_sound firstFamilyNodes firstFamilyNodes_checked node hnode', '',
        'theorem firstFamilyEndpoint_in_pool (lower : RSIndexLower) {n : ℕ} (hn : 2001 ≤ n)',
        '    (x : (Fin 24 × Fin 2) × Bool) : firstFamilyEndpoint x ∈ pool n := by',
        '  have hb := firstFamilyEndpoint_bounds x',
        '  exact finitePrefix_L_prime_in_pool lower (by omega) (firstFamilyEndpoint_prime x) hb.1 (by omega)', '',
        'def firstFamilyPoolValues (lower : RSIndexLower) {n : ℕ} (hn : 2001 ≤ n) :',
        '    (Fin 24 × Fin 2) × Bool → pool n := fun x =>',
        '  ⟨firstFamilyEndpoint x, firstFamilyEndpoint_in_pool lower hn x⟩', '',
        'theorem firstFamilyPoolValues_injective (lower : RSIndexLower) {n : ℕ} (hn : 2001 ≤ n) :',
        '    Function.Injective (firstFamilyPoolValues lower hn) := by',
        '  intro x y h',
        '  exact firstFamilyEndpoint_injective (congrArg Subtype.val h)', '',
        'theorem firstFamilyPoolValues_gap (lower : RSIndexLower) {n : ℕ} (hn : 2001 ≤ n)',
        '    (j : Fin 24) (i : Fin 2) :',
        '    (firstFamilyPoolValues lower hn ((j, i), true)).val =',
        '      (firstFamilyPoolValues lower hn ((j, i), false)).val + 2 ^ (j.val + 1) := by',
        '  simp [firstFamilyPoolValues, firstFamilyEndpoint]', '',
        'end Sude.GeneratedPrefix', '',
    ]
    rendered = '\n'.join(lines)
    if not OUT.exists() or OUT.read_text() != rendered:
        OUT.write_text(rendered)
    print(f'{len(rows)} source stages, {len(endpoints)} endpoints, {len(nodes)} Lucas nodes')


if __name__ == '__main__':
    main()
