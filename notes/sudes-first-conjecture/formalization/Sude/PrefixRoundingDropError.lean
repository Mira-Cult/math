import Mathlib.Tactic

/-! Drop-time error control for one line in simultaneous iterative rounding.
This lemma assumes the frozen-coordinate and box invariants; it does not
construct a rounding trajectory or the drop time. -/

namespace Sude
noncomputable section

/-- If changes after dropping are confined to the then-fractional slots,
then the final error of a line is bounded by its coefficient mass at drop.
The bound compares the two endpoints, not the total movement along the path. -/
theorem prefix_rounding_drop_error {α : Type*} [DecidableEq α]
    (slots active : Finset α) (a x y : α → ℝ)
    (hsub : active ⊆ slots)
    (ha : ∀ s ∈ active, 0 ≤ a s)
    (hx : ∀ s ∈ active, 0 ≤ x s ∧ x s ≤ 1)
    (hy : ∀ s ∈ active, 0 ≤ y s ∧ y s ≤ 1)
    (hfreeze : ∀ s ∈ slots, s ∉ active → y s = x s) :
    |∑ s ∈ slots, a s * (y s - x s)| ≤ ∑ s ∈ active, a s := by
  have heq : (∑ s ∈ slots, a s * (y s - x s)) =
      ∑ s ∈ active, a s * (y s - x s) := by
    symm
    apply Finset.sum_subset hsub
    intro s hs hnot
    simp [hfreeze s hs hnot]
  rw [heq]
  calc
    |∑ s ∈ active, a s * (y s - x s)| ≤
        ∑ s ∈ active, |a s * (y s - x s)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ active, a s := by
      apply Finset.sum_le_sum
      intro s hs
      have hdiff : |y s - x s| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> have := hx s hs <;> have := hy s hs <;> linarith
      rw [abs_mul, abs_of_nonneg (ha s hs)]
      nlinarith [mul_le_mul_of_nonneg_left hdiff (ha s hs)]

/-- The drop rule's scalar threshold immediately gives the final line error
once the equation was preserved up to the drop point. -/
theorem prefix_rounding_drop_error_bound {α : Type*} [DecidableEq α]
    (slots active : Finset α) (a x y : α → ℝ) (C : ℝ)
    (hsub : active ⊆ slots)
    (ha : ∀ s ∈ active, 0 ≤ a s)
    (hx : ∀ s ∈ active, 0 ≤ x s ∧ x s ≤ 1)
    (hy : ∀ s ∈ active, 0 ≤ y s ∧ y s ≤ 1)
    (hfreeze : ∀ s ∈ slots, s ∉ active → y s = x s)
    (hmass : (∑ s ∈ active, a s) ≤ 10*C) :
    |∑ s ∈ slots, a s * (y s - x s)| ≤ 10*C :=
  (prefix_rounding_drop_error slots active a x y hsub ha hx hy hfreeze).trans hmass

end
end Sude
