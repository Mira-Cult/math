#!/usr/bin/env python3
"""Emit Lean data for the first FTT row's Lucas closure; proves nothing itself."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SRC = ROOT / 'problems/prime-line-sums/inputs/cutoff2_finite_target_table_data.json'
DEST = ROOT / 'formalizations/sude/Sude/FirstTargetLucas.lean'

def main():
    data = json.loads(SRC.read_text())
    row = data['rows'][0]
    if row[:1] != [2001] or row[3:] != [65834615813, 65834631041, 65834630539]:
        raise ValueError('first FTT row does not match the pinned fixture')
    certificates = data['prime_certificates']
    todo = list(row[3:])
    closure = set()
    while todo:
        value = todo.pop()
        if value in closure:
            continue
        closure.add(value)
        todo.extend(pair[0] for pair in certificates[str(value)]['factors'])
    def node(n):
        cert = certificates[str(n)]
        factors = ', '.join(f'({q}, {e})' for q, e in cert['factors'])
        return f'⟨{n}, {cert["witness"]}, [{factors}]⟩'
    content = '''import Sude.LucasCertificate

/-! Source-derived fixture: exactly the recursive Lucas closure for the three
FTT targets at n=2001. Generator output is data, not proof. -/
namespace Sude.Lucas
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def firstTargetNodes : List Node := [
'''
    content += ',\n'.join('  ' + node(n) for n in sorted(closure))
    content += '''
]

theorem firstTargetNodes_accepted : checkCertificate firstTargetNodes = true := by
  decide +kernel

theorem firstTargets_prime : Nat.Prime 65834615813 ∧ Nat.Prime 65834631041 ∧
    Nat.Prime 65834630539 := by
  have h := checkCertificate_sound firstTargetNodes firstTargetNodes_accepted
  refine ⟨?_, ?_, ?_⟩
'''
    for n in row[3:]:
        content += f'  · exact h {node(n)} (by decide)\n'
    content += '''
-- Arithmetic for the first published row. These literals are not yet proved
-- to equal the prescribed pool's maximum or total.
theorem firstTarget_integer_controls :
    (2001 - 2) * 65834615813 + 65834631041 + 65834630539 = 131735066271767 ∧
    1000 * |(2001 * 65834615813 : ℤ) - 131735066271767| ≤ 2001 * 67939607 ∧
    1000 * |(2001 * 65834631041 : ℤ) - 131735066271767| ≤ 2001 * 67939607 ∧
    1000 * |(2001 * 65834630539 : ℤ) - 131735066271767| ≤ 2001 * 67939607 ∧
    121 * 2001 ^ 2 * 67939607 < 250 * 131735066271767 ∧
    125 * 131735066271767 < 61 * 2001 ^ 2 * 67939607 := by
  norm_num

end Sude.Lucas
'''
    DEST.write_text(content)
    print(f'wrote {DEST.relative_to(ROOT)}: {len(closure)} certificate nodes')

if __name__ == '__main__':
    main()
