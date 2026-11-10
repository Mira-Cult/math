import PASoundness.PeanoFreeNamePermutation

/-! Explicit finite swaps moving the six canonical low names to a fresh
block. This is name arithmetic, not a theorem of PA or of AX8. -/
namespace PASoundness.PeanoFreeNameVacate
open PeanoFreeNamePermutation

/-- Move names 0,...,5 into the disjoint block starting at k. -/
def vacate (k : Nat) : List (Nat × Nat) :=
  [(0,k), (1,k+1), (2,k+2), (3,k+3), (4,k+4), (5,k+5)]

/-- Names outside both swapped blocks remain unchanged. -/
theorem outside_action (k n : Nat) (hk : 6 ≤ k) (hn : 6 ≤ n)
    (hblock : n < k ∨ k+6 ≤ n) : applyName (vacate k) n = n := by
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  have h3 : n ≠ 3 := by omega
  have h4 : n ≠ 4 := by omega
  have h5 : n ≠ 5 := by omega
  have hk0 : n ≠ k := by omega
  have hk1 : n ≠ k+1 := by omega
  have hk2 : n ≠ k+2 := by omega
  have hk3 : n ≠ k+3 := by omega
  have hk4 : n ≠ k+4 := by omega
  have hk5 : n ≠ k+5 := by omega
  simp [vacate, applyName, h0, h1, h2, h3, h4, h5, hk0, hk1, hk2, hk3, hk4, hk5]

end PASoundness.PeanoFreeNameVacate
