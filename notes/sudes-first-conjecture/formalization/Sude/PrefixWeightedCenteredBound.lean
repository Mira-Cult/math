import Sude.CentralWindow

/-! Weighted centered-sum control for a finite family of pair slots.
This does not establish physical incidence, midpoint widths, or an allocation. -/
namespace Sude
noncomputable section

/-- Nonnegative weights with total at most two, applied to deviations bounded
in absolute value by `C`, give one aggregate bound `2*C`. -/
theorem prefix_weighted_centered_bound {α : Type*}
    (S : Finset α) (weight deviation : α → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hw : ∀ i ∈ S, 0 ≤ weight i)
    (hmass : (∑ i ∈ S, weight i) ≤ 2)
    (hdev : ∀ i ∈ S, |deviation i| ≤ C) :
    |∑ i ∈ S, weight i * deviation i| ≤ 2 * C := by
  calc
    |∑ i ∈ S, weight i * deviation i| ≤ ∑ i ∈ S, |weight i * deviation i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, weight i * C := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]
      exact mul_le_mul_of_nonneg_left (hdev i hi) (hw i hi)
    _ = (∑ i ∈ S, weight i) * C := (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * C := mul_le_mul_of_nonneg_right hmass hC

end
end Sude
