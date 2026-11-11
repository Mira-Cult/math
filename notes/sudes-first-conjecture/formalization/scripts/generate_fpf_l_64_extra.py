#!/usr/bin/env python3
"""Generate checked evidence for L pairs 33–64, reusing the first 32.

Hashes bind the input stream; all mathematical properties are checked by Lean.
This remains a finite slice, not acceptance of the full FPF population.
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
OUT = ROOT / 'formalizations/sude/Sude/GeneratedPrefix/L64Extra'
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
    with tempfile.TemporaryDirectory(prefix='sude-fpf-l64-') as tmp:
        binary, stem = Path(tmp) / 'generator', Path(tmp) / 'population'
        subprocess.run([compiler, '-O3', '-std=c++17', str(CPP), '-o', str(binary)], check=True)
        subprocess.run([str(binary), str(stem), '60000000', '14448', '24', '13000000', '55000000'],
                       check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stream = stem.with_suffix('.bin').read_bytes()
    if hashlib.sha256(stream).hexdigest() != profile['stream_sha256'] or len(stream) != 4 * 24 * 14448:
        raise ValueError('reproduced stream digest or length mismatch')
    source = struct.unpack('<' + str(len(stream) // 4) + 'I', stream)
    lows = [source[j * 14448 + 32:j * 14448 + 64] for j in range(24)]
    chunks = [[p for low in row for p in (low, low + 2 ** (j + 1))]
              for j, row in enumerate(lows)]
    OUT.mkdir(parents=True, exist_ok=True)
    for j, chunk in enumerate(chunks):
        imports = ['import Sude.GeneratedPrefix.L32Distinct.Stage23'] if j == 0 else [
            f'import Sude.GeneratedPrefix.L64Extra.DistinctStage{j - 1:02d}']
        lines = imports + ['', 'namespace Sude.GeneratedPrefix.L64Extra',
            'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '',
            f'def values{j:02d} : List ℕ := [' + ', '.join(map(str, chunk)) + ']', '']
        if j == 0:
            lines += ['def state00 : DistinctTrie := L32Distinct.state24', '']
        lines += [f'def state{j + 1:02d} : DistinctTrie :=',
            f'  DistinctTrie.insertAll 32 state{j:02d} values{j:02d}', '',
            f'theorem checked{j:02d} : distinctTrieAux 32 values{j:02d} state{j:02d} = true := by',
            '  decide +kernel', '',
            f'theorem step{j:02d} : DistinctTrie.advance 32 state{j:02d} values{j:02d} = some state{j + 1:02d} :=',
            f'  DistinctTrie.advance_of_check 32 state{j:02d} values{j:02d} checked{j:02d}', '',
            'end Sude.GeneratedPrefix.L64Extra', '']
        write(OUT / f'DistinctStage{j:02d}.lean', '\n'.join(lines))
    row_lit = ', '.join('![' + ', '.join(map(str, row)) + ']' for row in lows)
    names = ', '.join(f'values{j:02d}' for j in range(24))
    lines = ['import Sude.GeneratedPrefix.L64Extra.DistinctStage23',
        'import Sude.GeneratedPrefix.L32Distinct.All', 'import Sude.TrieChunkAppend', '',
        '/-! Distinctness of the first 64 source pairs per stage; primality is separate. -/',
        'namespace Sude.GeneratedPrefix.L64Extra', 'set_option maxRecDepth 100000',
        'set_option maxHeartbeats 0', '',
        'def lows : Fin 24 → Fin 32 → ℕ := ![' + row_lit + ']', '',
        'def endpoint (x : (Fin 24 × Fin 32) × Bool) : ℕ :=',
        '  lows x.1.1 x.1.2 + if x.2 then 2 ^ (x.1.1.val + 1) else 0', '',
        'def chunks : List (List ℕ) := [' + names + ']', '',
        'theorem checkpoints : VerifiedTrieChunks 32 state00 chunks state24 := by',
        '  unfold chunks']
    lines += [f'  apply VerifiedTrieChunks.cons step{j:02d}' for j in range(24)]
    lines += ['  exact VerifiedTrieChunks.nil _', '',
        'theorem flatten_eq_enumeration : chunks.flatten =',
        '    List.ofFn (endpoint ∘ (prefixEndpointIndexEquiv 24 32).symm) := by',
        '  decide +kernel', '',
        'theorem both_enumerations_nodup :',
        '    (List.ofFn (L32Distinct.endpoint ∘ (prefixEndpointIndexEquiv 24 32).symm) ++',
        '     List.ofFn (endpoint ∘ (prefixEndpointIndexEquiv 24 32).symm)).Nodup := by',
        '  have h := (VerifiedTrieChunks.append L32Distinct.checkpoints checkpoints).nodup',
        '  simpa only [List.flatten_append, L32Distinct.flatten_eq_enumeration, flatten_eq_enumeration] using h', '',
        'theorem both_injective : Function.Injective (Sum.elim L32Distinct.endpoint endpoint) :=',
        '  sumFamily_injective_of_nodup (prefixEndpointIndexEquiv 24 32).symm',
        '    (prefixEndpointIndexEquiv 24 32).symm L32Distinct.endpoint endpoint both_enumerations_nodup', '',
        'end Sude.GeneratedPrefix.L64Extra', '']
    write(OUT / 'DistinctAll.lean', '\n'.join(lines))
    spec = importlib.util.spec_from_file_location('first_tail_generator', HELPER)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
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
        imports = ['import Sude.LucasCertificate', 'import Sude.GeneratedPrefix.L64Extra.DistinctAll']
        if j:
            imports.append(f'import Sude.GeneratedPrefix.L64Extra.PrimeStage{j - 1:02d}')
        stage = imports + ['', f'namespace Sude.GeneratedPrefix.L64Extra.PrimeStage{j:02d}',
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
            f'end Sude.GeneratedPrefix.L64Extra.PrimeStage{j:02d}', '']
        write(OUT / f'PrimeStage{j:02d}.lean', '\n'.join(stage))
    all_lines = ['import Sude.GeneratedPrefix.L64Extra.PrimeStage23',
        'import Sude.GeneratedPrefix.L32Primes.All', '',
        '/-! The first 64 source pairs per L stage; full FPF acceptance remains open. -/',
        'namespace Sude.GeneratedPrefix.L64Extra',
        'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '',
        'theorem extra_prime (x : (Fin 24 × Fin 32) × Bool) : Nat.Prime (endpoint x) := by',
        '  rcases x with ⟨⟨j, i⟩, side⟩', '  fin_cases j']
    all_lines += [f'  · exact PrimeStage{j:02d}.prime i side' for j in range(24)]
    all_lines += ['', 'end Sude.GeneratedPrefix.L64Extra', '']
    write(OUT / 'All.lean', '\n'.join(all_lines))
    print(f'24 extra stages, 768 additional pairs, 1536 endpoints, {total} stage-local Lucas nodes')


if __name__ == '__main__':
    main()
