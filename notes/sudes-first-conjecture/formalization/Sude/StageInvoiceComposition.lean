import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Combine a per-stage ordinary invoice with a global rectangle invoice. -/
namespace Sude
noncomputable section

/-- If ordinary pair weights have squared sum at most `3d` in each stage,
while all rectangle squared weights together cost at most four, the actual
stage widths give the source's weighted invoice. The hypotheses must be
proved from the physical, disjoint pair-slot incidences. -/
theorem stage_squared_invoice_of_ordinary_and_rectangles {P : ℕ}
    (width ordinary rectangle : Fin P → ℝ) (d z : ℝ)
    (hord : ∀ j, ordinary j ≤ 3 * d)
    (hrect : ∀ j, 0 ≤ rectangle j)
    (hrectsum : (∑ j, rectangle j) ≤ 4)
    (hwidth : ∀ j, (width j) ^ 2 ≤ z ^ 2) :
    (∑ j, (width j) ^ 2 * (ordinary j + rectangle j)) ≤
      3 * d * (∑ j, (width j) ^ 2) + 4 * z ^ 2 := by
  have hp : ∀ j, (width j) ^ 2 * (ordinary j + rectangle j) ≤
      3 * d * (width j) ^ 2 + z ^ 2 * rectangle j := by
    intro j
    have h₁ := mul_nonneg (sq_nonneg (width j)) (sub_nonneg.mpr (hord j))
    have h₂ := mul_nonneg (sub_nonneg.mpr (hwidth j)) (hrect j)
    nlinarith
  calc
    _ ≤ ∑ j, (3 * d * (width j) ^ 2 + z ^ 2 * rectangle j) :=
      Finset.sum_le_sum (by intro j _; exact hp j)
    _ = 3 * d * (∑ j, (width j) ^ 2) + z ^ 2 * (∑ j, rectangle j) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 3 * d * (∑ j, (width j) ^ 2) + 4 * z ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hrectsum (sq_nonneg z)
      nlinarith

end
end Sude
