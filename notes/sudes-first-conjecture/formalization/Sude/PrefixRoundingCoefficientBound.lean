import Sude.CentralWindow

/-! The fixed DP2 line coefficients inherit the global slot-weight budget.
No rounding, stage assignment, or discrepancy theorem is asserted here. -/
namespace Sude
noncomputable section

/-- If each line weight is nonnegative, the total weight of a slot is at
most five, and its group width lies in `[0,C]`, then the fixed coefficient
`w l s * delta (group s)` is nonnegative and has total mass at most `5*C`.
The sum is over all supplied lines, jointly across all groups. -/
theorem prefix_rounding_coefficient_bound {S G L : Type*}
    (U : Finset S) (lines : Finset L) (group : S → G)
    (w : L → S → ℝ) (delta : G → ℝ) (C : ℝ)
    (hw : ∀ l ∈ lines, ∀ s ∈ U, 0 ≤ w l s)
    (hweight : ∀ s ∈ U, (∑ l ∈ lines, w l s) ≤ 5)
    (hdelta : ∀ s ∈ U, 0 ≤ delta (group s) ∧ delta (group s) ≤ C) :
    (∀ l ∈ lines, ∀ s ∈ U, 0 ≤ w l s * delta (group s)) ∧
    (∀ s ∈ U, (∑ l ∈ lines, w l s * delta (group s)) ≤ 5 * C) := by
  constructor
  · intro l hl s hs
    exact mul_nonneg (hw l hl s hs) (hdelta s hs).1
  · intro s hs
    calc
      (∑ l ∈ lines, w l s * delta (group s)) =
          (∑ l ∈ lines, w l s) * delta (group s) := by rw [Finset.sum_mul]
      _ ≤ 5 * delta (group s) :=
        mul_le_mul_of_nonneg_right (hweight s hs) (hdelta s hs).1
      _ ≤ 5 * C := mul_le_mul_of_nonneg_left (hdelta s hs).2 (by norm_num)

end
end Sude
