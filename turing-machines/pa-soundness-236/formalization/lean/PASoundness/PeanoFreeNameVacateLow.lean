import PASoundness.PeanoFreeNamePermutation

/-! Pointwise low-name behavior of six disjoint swaps. -/
namespace PASoundness.PeanoFreeNameVacateLow
open PeanoFreeNamePermutation

def block (k : Nat) : List (Nat × Nat) :=
  [(0,k), (1,k+1), (2,k+2), (3,k+3), (4,k+4), (5,k+5)]

private theorem skip {x y n : Nat} {xs : List (Nat × Nat)}
    (h1 : n ≠ x) (h2 : n ≠ y) :
    applyName ((x,y) :: xs) n = applyName xs n := by
  simp [applyName, h1, h2]

private theorem hit {x y : Nat} {xs : List (Nat × Nat)} :
    applyName ((x,y) :: xs) x = applyName xs y := by
  simp [applyName]

/-- If the target block begins at or above 6, each low name is sent to the
same offset of the target block. This is a finite name calculation. -/
theorem low_action (k n : Nat) (hk : 6 ≤ k) (hn : n < 6) :
    applyName (block k) n = k+n := by
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hcases with h | h | h | h | h | h <;> subst n <;>
    simp only [block] <;>
    (repeat' first | rw [hit] | (rw [skip] <;> try omega)) <;>
    try simp [applyName]

end PASoundness.PeanoFreeNameVacateLow

#print axioms PASoundness.PeanoFreeNameVacateLow.low_action
