#!/usr/bin/env python3
"""Generate finite Lean regression proofs from the frozen independent reference.

The reference supplies expected finite values, not an oracle for an unbounded
semantics or a proof of the register program or physical machine.
"""
import hashlib
import importlib.util
from pathlib import Path
import random
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REFERENCE = ROOT / 'bindings/m236/semantic_reference.py'
SHA256 = 'ba4786c9363b66db0a9528328b9ac05b2f0ab95f68e0bd7d0db61554d5dfafa7'
if hashlib.sha256(REFERENCE.read_bytes()).hexdigest() != SHA256:
    raise SystemExit('reference hash mismatch')
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('m236_reference', REFERENCE)
reference = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reference)

rng = random.Random(236)
cases = []
for rank in range(1, 9):
    for formula in range(16):
        if rank == 1:
            coords = [rng.randrange(8)]
        else:
            # Sample both inside and outside the finite support; witness bits,
            # signs, branch moves and unused suffixes are intentionally varied.
            coords = [rng.randrange(32), rng.randrange(rank + 1)]
            coords.extend(rng.randrange(4) for _ in range(rank - 2))
        result = reference.record(rank, formula, coords, prefix='numeric',
                                  syntax='cantor', atoms='strict', atom_slot=True)
        cases.append((rank, formula, coords, result))

lines = [
    'import PASoundness.M236Game',
    'open PASoundness.M236Game',
    'set_option maxRecDepth 8192',
    'set_option maxHeartbeats 1000000',
    'set_option linter.unusedSimpArgs false',
]
for rank, formula, coords, result in cases:
    values = ', '.join(str(x) for x in coords)
    value = 'true' if result else 'false'
    lines += [f'example : selectedValue ⟨{rank}, {formula}, [{values}]⟩ = {value} := by',
              '  simp (config := { decide := true }) [selectedValue, aligned, path, atom,',
              '    tag, payload, PASoundness.Cantor.unpair, PASoundness.Cantor.unpairAux]']
with tempfile.TemporaryDirectory(prefix='m236-game-') as td:
    lean = Path(td) / 'Fixtures.lean'
    lean.write_text('\n'.join(lines) + '\n', encoding='utf-8')
    subprocess.run(['lake', 'env', 'lean', str(lean)], cwd=ROOT / 'lean', check=True)
print(f'{len(cases)} finite source-reference cases checked by Lean; '
      f'{sum(x[3] for x in cases)} have rejection bit 1')
