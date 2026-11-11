import Sude.LucasCertificate

/-! Source-derived fixture: exactly the recursive Lucas closure for the three
FTT targets at n=2001. Generator output is data, not proof. -/
namespace Sude.Lucas
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def firstTargetNodes : List Node := [
  ⟨2, 1, []⟩,
  ⟨3, 2, [(2, 1)]⟩,
  ⟨5, 2, [(2, 2)]⟩,
  ⟨7, 3, [(2, 1), (3, 1)]⟩,
  ⟨11, 2, [(2, 1), (5, 1)]⟩,
  ⟨13, 2, [(2, 2), (3, 1)]⟩,
  ⟨17, 3, [(2, 4)]⟩,
  ⟨23, 5, [(2, 1), (11, 1)]⟩,
  ⟨79, 3, [(2, 1), (3, 1), (13, 1)]⟩,
  ⟨89, 3, [(2, 3), (11, 1)]⟩,
  ⟨113, 3, [(2, 4), (7, 1)]⟩,
  ⟨179, 2, [(2, 1), (89, 1)]⟩,
  ⟨181, 2, [(2, 2), (3, 2), (5, 1)]⟩,
  ⟨271, 6, [(2, 1), (3, 3), (5, 1)]⟩,
  ⟨359, 7, [(2, 1), (179, 1)]⟩,
  ⟨719, 11, [(2, 1), (359, 1)]⟩,
  ⟨1627, 3, [(2, 1), (3, 1), (271, 1)]⟩,
  ⟨1811, 6, [(2, 1), (5, 1), (181, 1)]⟩,
  ⟨3391, 3, [(2, 1), (3, 1), (5, 1), (113, 1)]⟩,
  ⟨3457, 7, [(2, 7), (3, 3)]⟩,
  ⟨3235753, 5, [(2, 3), (3, 2), (13, 1), (3457, 1)]⟩,
  ⟨335890897, 5, [(2, 4), (3, 1), (11, 1), (17, 1), (23, 1), (1627, 1)]⟩,
  ⟨65834615813, 2, [(2, 2), (7, 2), (335890897, 1)]⟩,
  ⟨65834630539, 2, [(2, 1), (3, 1), (3391, 1), (3235753, 1)]⟩,
  ⟨65834631041, 3, [(2, 7), (5, 1), (79, 1), (719, 1), (1811, 1)]⟩
]

theorem firstTargetNodes_accepted : checkCertificate firstTargetNodes = true := by
  decide +kernel

theorem firstTargets_prime : Nat.Prime 65834615813 ∧ Nat.Prime 65834631041 ∧
    Nat.Prime 65834630539 := by
  have h := checkCertificate_sound firstTargetNodes firstTargetNodes_accepted
  refine ⟨?_, ?_, ?_⟩
  · exact h ⟨65834615813, 2, [(2, 2), (7, 2), (335890897, 1)]⟩ (by decide)
  · exact h ⟨65834631041, 3, [(2, 7), (5, 1), (79, 1), (719, 1), (1811, 1)]⟩ (by decide)
  · exact h ⟨65834630539, 2, [(2, 1), (3, 1), (3391, 1), (3235753, 1)]⟩ (by decide)

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
