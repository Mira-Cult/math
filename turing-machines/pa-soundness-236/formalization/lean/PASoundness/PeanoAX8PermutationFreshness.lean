import PASoundness.PeanoFreeNameFreshness

/-! Fresh canonical selector names after an explicit AX8 name permutation.
The permutation's construction and the literal AX8 theorem are separate. -/
namespace PASoundness.PeanoAX8PermutationFreshness
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic

/-- If the input and outer names map to 4 and 5, the output name is absent
from the original formula, and all remaining supported names map above 5,
then the permuted formula has no free name below 4. This retains every other
parameter via the supplied swap-list action. -/
theorem fresh_below_four (xs : List (Nat × Nat)) (φ : Peano.Formula)
    (a b c : Nat)
    (ha : PeanoFreeNamePermutation.applyName xs a = 4)
    (hb : PeanoFreeNamePermutation.applyName xs b = 5)
    (hc : c ∉ φ.freeVarFinset)
    (hother : ∀ y ∈ φ.freeVarFinset, y ≠ a → y ≠ b → y ≠ c →
      6 ≤ PeanoFreeNamePermutation.applyName xs y)
    (z : Nat) (hz : z < 4) :
    z ∉ (PeanoFreeNamePermutation.applyFormula xs φ).freeVarFinset := by
  apply PeanoFreeNameFreshness.permuted_fresh
  intro y hy
  by_cases hya : y = a
  · subst y
    rw [ha]
    omega
  by_cases hyb : y = b
  · subst y
    rw [hb]
    omega
  by_cases hyc : y = c
  · subst y
    exact False.elim (hc hy)
  have hlarge := hother y hy hya hyb hyc
  omega

end PASoundness.PeanoAX8PermutationFreshness

#print axioms PASoundness.PeanoAX8PermutationFreshness.fresh_below_four
