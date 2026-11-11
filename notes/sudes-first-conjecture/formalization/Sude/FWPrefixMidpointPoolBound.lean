import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Conditional midpoint and finite-stage mean bounds for the FW prefix.

The pool mean enclosure and the range of every supplied midpoint are explicit
inputs. In particular, this file does not establish that the physical growth
construction supplies midpoints in the required range. -/

namespace Sude
noncomputable section

/-- The FW mean enclosure controls any supplied value in the pool interval. -/
theorem fw_prefix_value_pool_bound (X μ x : ℝ) (hX : 0 ≤ X)
    (hμlo : (243 / 500 : ℝ) * X ≤ μ)
    (hμhi : μ ≤ (123 / 250 : ℝ) * X)
    (hxlo : 0 ≤ x) (hxhi : x ≤ X) :
    |x - μ| ≤ (257 / 500 : ℝ) * X := by
  rw [abs_le]
  constructor <;> linarith

/-- A nonempty finite stage whose entries lie in `[0,X]` has its mean there. -/
theorem fw_prefix_stage_average_range {Q : ℕ} (hQ : 0 < Q)
    (X : ℝ) (values : Fin Q → ℝ)
    (hvalues : ∀ i, 0 ≤ values i ∧ values i ≤ X) :
    0 ≤ (∑ i, values i) / (Q : ℝ) ∧
      (∑ i, values i) / (Q : ℝ) ≤ X := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => (hvalues i).1) hQr.le
  · apply (div_le_iff₀ hQr).2
    calc
      ∑ i, values i ≤ ∑ _i : Fin Q, X := by
        exact Finset.sum_le_sum fun i _ => (hvalues i).2
      _ = X * (Q : ℝ) := by simp [mul_comm]

/-- Every supplied nonempty stage mean satisfies the same prefix bound. -/
theorem fw_prefix_stage_mean_pool_bound {Q : ℕ} (hQ : 0 < Q)
    (X μ : ℝ) (values : Fin Q → ℝ) (hX : 0 ≤ X)
    (hμlo : (243 / 500 : ℝ) * X ≤ μ)
    (hμhi : μ ≤ (123 / 250 : ℝ) * X)
    (hvalues : ∀ i, 0 ≤ values i ∧ values i ≤ X) :
    |(∑ i, values i) / (Q : ℝ) - μ| ≤ (257 / 500 : ℝ) * X := by
  obtain ⟨hlo, hhi⟩ := fw_prefix_stage_average_range hQ X values hvalues
  exact fw_prefix_value_pool_bound X μ _ hX hμlo hμhi hlo hhi

/-- Any supplied finite set of stage-mean deviations has the triangle bound. -/
theorem fw_prefix_stage_means_sum_pool_bound {I : Type*} (stages : Finset I)
    {Q : ℕ} (hQ : 0 < Q) (X μ : ℝ) (values : I → Fin Q → ℝ)
    (hX : 0 ≤ X) (hμlo : (243 / 500 : ℝ) * X ≤ μ)
    (hμhi : μ ≤ (123 / 250 : ℝ) * X)
    (hvalues : ∀ j ∈ stages, ∀ i, 0 ≤ values j i ∧ values j i ≤ X) :
    |∑ j ∈ stages, ((∑ i, values j i) / (Q : ℝ) - μ)| ≤
      (stages.card : ℝ) * ((257 / 500 : ℝ) * X) := by
  calc
    _ ≤ ∑ j ∈ stages, |(∑ i, values j i) / (Q : ℝ) - μ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ stages, ((257 / 500 : ℝ) * X) := by
      apply Finset.sum_le_sum
      intro j hj
      exact fw_prefix_stage_mean_pool_bound hQ X μ (values j) hX hμlo hμhi (hvalues j hj)
    _ = _ := by simp

end
end Sude
