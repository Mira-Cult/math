#!/usr/bin/env python3
"""Generate checked trie checkpoints for the first 32 pairs of each L stage.

The original stream is regenerated and hash-checked. Lean checks each
checkpoint and global distinctness. Primality is outside this certificate.
"""
import hashlib
import json
import shutil
import struct
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MANIFEST = ROOT / 'problems/prime-line-sums/inputs/cutoff2_finite_prefix_family_inputs.json'
CPP = ROOT / 'problems/prime-line-sums/code/cutoff2_finite_prefix_family_generator.cpp'
OUT = ROOT / 'formalizations/sude/Sude/GeneratedPrefix/L32Distinct'
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
    with tempfile.TemporaryDirectory(prefix='sude-fpf-l32-') as tmp:
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
    chunks = [[p for low in row for p in (low, low + 2 ** (j + 1))]
              for j, row in enumerate(lows)]
    if len(set(sum(chunks, []))) != 1536:
        raise ValueError('source slice has repeated endpoints')
    OUT.mkdir(parents=True, exist_ok=True)
    for j, chunk in enumerate(chunks):
        imports = ['import Sude.FiniteDistinctChunks'] if j == 0 else [
            f'import Sude.GeneratedPrefix.L32Distinct.Stage{j - 1:02d}']
        lines = imports + ['', 'namespace Sude.GeneratedPrefix.L32Distinct',
            'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '',
            f'def values{j:02d} : List ℕ := [' + ', '.join(map(str, chunk)) + ']', '']
        if j == 0:
            lines += ['def state00 : DistinctTrie := .empty', '']
        lines += [f'def state{j + 1:02d} : DistinctTrie :=',
            f'  DistinctTrie.insertAll 32 state{j:02d} values{j:02d}', '',
            f'theorem checked{j:02d} : distinctTrieAux 32 values{j:02d} state{j:02d} = true := by',
            '  decide +kernel', '',
            f'theorem step{j:02d} : DistinctTrie.advance 32 state{j:02d} values{j:02d} = some state{j + 1:02d} :=',
            f'  DistinctTrie.advance_of_check 32 state{j:02d} values{j:02d} checked{j:02d}', '',
            'end Sude.GeneratedPrefix.L32Distinct', '']
        write(OUT / f'Stage{j:02d}.lean', '\n'.join(lines))
    rows = ', '.join('![' + ', '.join(map(str, row)) + ']' for row in lows)
    names = ', '.join(f'values{j:02d}' for j in range(24))
    all_lines = ['import Sude.GeneratedPrefix.L32Distinct.Stage23', '',
        '/-! Distinctness only: the 1,536 source-slice endpoints have not all been certified prime. -/',
        'namespace Sude.GeneratedPrefix.L32Distinct', 'set_option maxRecDepth 100000',
        'set_option maxHeartbeats 0', '',
        'def lows : Fin 24 → Fin 32 → ℕ := ![' + rows + ']', '',
        'def endpoint (x : (Fin 24 × Fin 32) × Bool) : ℕ :=',
        '  lows x.1.1 x.1.2 + if x.2 then 2 ^ (x.1.1.val + 1) else 0', '',
        'def chunks : List (List ℕ) := [' + names + ']', '',
        'theorem checkpoints : VerifiedTrieChunks 32 state00 chunks state24 := by',
        '  unfold chunks']
    all_lines += [f'  apply VerifiedTrieChunks.cons step{j:02d}' for j in range(24)]
    all_lines += ['  exact VerifiedTrieChunks.nil _', '',
        'theorem endpoints_nodup : chunks.flatten.Nodup := checkpoints.nodup', '',
        'theorem flatten_eq_enumeration : chunks.flatten =',
        '    List.ofFn (endpoint ∘ (prefixEndpointIndexEquiv 24 32).symm) := by',
        '  decide +kernel', '',
        'theorem endpoint_injective : Function.Injective endpoint := by',
        '  have h := endpoints_nodup', '  rw [flatten_eq_enumeration, List.ofFn_eq_map] at h',
        '  have hi := (List.nodup_map_iff_inj_on (List.nodup_finRange (24 * 32 * 2))).mp h',
        '  apply ((prefixEndpointIndexEquiv 24 32).symm.injective_comp endpoint).mp',
        '  intro a b hab', '  exact hi a (List.mem_finRange a) b (List.mem_finRange b) hab', '',
        'end Sude.GeneratedPrefix.L32Distinct', '']
    write(OUT / 'All.lean', '\n'.join(all_lines))
    print('24 checked chunks requested; 768 pairs and 1536 endpoint values')


if __name__ == '__main__':
    main()
