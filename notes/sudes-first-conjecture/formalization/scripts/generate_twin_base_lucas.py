#!/usr/bin/env python3
"""Generate checked Lucas nodes for base primes absent from the FTT prefix.

All generated values and witnesses are untrusted; Lean checks every node.
Run from formalizations/sude in the pinned environment.
"""
from pathlib import Path
from math import gcd, isqrt
import re

LIMIT = 32768
MAX_NODES = 150
ftt = Path('Sude/GeneratedFTT')
out = Path('Sude/GeneratedTwinBase')
out.mkdir(parents=True, exist_ok=True)
known = {}
for i in range(151):
    path = ftt / f'N{i:04}.lean'
    for value in re.findall(r'theorem prime_(\d+)\b', path.read_text()):
        value = int(value)
        if value in known:
            raise ValueError(f'duplicate FTT node {value}')
        known[value] = f'Sude.GeneratedFTT.N{i:04}'
flags = bytearray([1]) * (LIMIT + 1)
flags[:2] = b'\x00\x00'
for p in range(2, isqrt(LIMIT) + 1):
    if flags[p]:
        for j in range(p * p, LIMIT + 1, p):
            flags[j] = 0
primes = [p for p in range(2, LIMIT + 1) if flags[p]]
missing = [p for p in primes if p not in known]

def factor(n):
    result = []
    for p in primes:
        if p * p > n:
            break
        if n % p == 0:
            power = 0
            while n % p == 0:
                n //= p
                power += 1
            result.append((p, power))
    if n > 1:
        result.append((n, 1))
    return result

for start in range(0, len(missing), MAX_NODES):
    values = missing[start:start + MAX_NODES]
    name = f'M{start // MAX_NODES:03}'
    facs = {p: factor(p - 1) for p in values}
    dependencies = sorted({known[q] for p in values for q, _ in facs[p] if q in known})
    lines = ['import Sude.LucasCertificate'] + [f'import {d}' for d in dependencies]
    lines += ['', '/-! Generated Lucas nodes for the FT base; checked by Lean. -/',
              'namespace Sude.Lucas.Generated', 'set_option maxRecDepth 10000',
              'set_option maxHeartbeats 0', '']
    for p in values:
        factors = facs[p]
        if not all(q in known or q in values[:values.index(p)] for q, _ in factors):
            raise ValueError(f'missing factor proof for {p}')
        witness = next(a for a in range(2, p)
                       if pow(a, p - 1, p) == 1 and
                       all(gcd(pow(a, (p - 1) // q, p) - 1, p) == 1 for q, _ in factors))
        qs = ', '.join(str(q) for q, _ in factors)
        pairs = ', '.join(f'({q}, {e})' for q, e in factors)
        lines += [f'theorem prime_{p} : Nat.Prime {p} := by',
                  f'  apply nodeValid_prime [{qs}] ⟨{p}, {witness}, [{pairs}]⟩',
                  '  · intro q hq',
                  '    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq',
                  '    rcases hq with ' + ' | '.join('rfl' for _ in factors)]
        if len(factors) == 1:
            lines.append(f'    exact prime_{factors[0][0]}')
        else:
            lines += [f'    · exact prime_{q}' for q, _ in factors]
        lines += ['  · decide +kernel', '']
    lines.append('end Sude.Lucas.Generated')
    (out / f'{name}.lean').write_text('\n'.join(lines) + '\n')
    known.update({p: f'Sude.GeneratedTwinBase.{name}' for p in values})
print(f'{len(primes)} primes, {len(missing)} new Lucas nodes, {(len(missing)+MAX_NODES-1)//MAX_NODES} modules')

# Build independently checkable blocks whose proofs use the certified nodes.
odd = [p for p in primes if p != 2]
block_size = 64
names = []
for start in range(0, len(odd), block_size):
    values = odd[start:start + block_size]
    name = f'B{start // block_size:03}'
    names.append(name)
    deps = sorted({known[p] for p in values})
    lines = [f'import {d}' for d in deps]
    if start // block_size >= 2:
        lines.append(f'import Sude.GeneratedTwinBase.B{start // block_size - 2:03}')
    lines += ['', '/-! Generated FT base block; all prime proofs are kernel checked. -/',
              'namespace Sude.Lucas.Generated', f'namespace {name}',
              'set_option maxRecDepth 10000', 'set_option maxHeartbeats 0', '',
              'def values : List ℕ := [' + ', '.join(map(str, values)) + ']', '',
              'theorem valid : values.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by',
              '  simp only [values, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_nil, and_true]',
              '  exact ⟨']
    lines += [f'    ⟨prime_{p}, by decide, by decide⟩' + (',' if i + 1 < len(values) else '')
              for i, p in enumerate(values)]
    lines += ['  ⟩', '', f'end {name}', 'end Sude.Lucas.Generated']
    (out / f'{name}.lean').write_text('\n'.join(lines) + '\n')

imports = ['import Sude.FiniteTwinOddBaseData'] + [f'import Sude.GeneratedTwinBase.{name}' for name in names]
lines = imports + ['', '/-! The generated FT base is certified by checked Lucas nodes. -/',
                   'namespace Sude', 'open Sude.Lucas.Generated', 'set_option maxRecDepth 100000',
                   'set_option maxHeartbeats 0', '',
                   'def finiteTwinOddBaseBlocks : List (List ℕ) := [']
lines += [f'  {name}.values' + (',' if i + 1 < len(names) else '') for i, name in enumerate(names)]
lines += [']', '',
          'theorem finiteTwinOddBase_blocks : finiteTwinOddBase = finiteTwinOddBaseBlocks.flatten := by',
          '  rfl', '',
          'theorem finiteTwinOddBase_all :',
          '    finiteTwinOddBase.all (fun p => decide (Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768)) = true := by',
          '  rw [finiteTwinOddBase_blocks, List.all_flatten]',
          '  simp only [finiteTwinOddBaseBlocks, List.all_cons, List.all_nil,']
lines += [f'    {name}.valid,' for name in names]
lines += ['    Bool.true_and]', '', 'end Sude']
Path('Sude/FiniteTwinOddBaseLucas.lean').write_text('\n'.join(lines) + '\n')
print(f'{len(names)} independently checked prime-list blocks')
