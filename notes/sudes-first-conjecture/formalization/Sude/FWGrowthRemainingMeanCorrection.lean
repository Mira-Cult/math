import Sude.PrefixSelectionMeanShift

/-! Exact aggregate recentering after reserving 48 growth labels per stage.
No claim of a pointwise mean shift or physical line bound is made. -/
namespace Sude
noncomputable section

/-- Removing 48 labels from each population of size `6*(n+8)` shifts the
sum of remaining means by exactly minus the aggregate selected discrepancy
divided by `6*n`. Every stage may have a different mean. -/
theorem fw_growth_remaining_mean_shift {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (n : ℕ) (hn : 0 < n) (A R : ι → Finset α) (v : ι → α → ℝ)
    (hA : ∀ j, (A j).card = 6 * (n+8))
    (hR : ∀ j, R j ⊆ A j) (hcard : ∀ j, (R j).card = 48) :
    let μ := fun j => (∑ x ∈ A j, v j x) / (6 * (n+8) : ℕ)
    let μ' := fun j => (∑ x ∈ A j \ R j, v j x) / (6*n : ℕ)
    let E := (∑ j, ∑ x ∈ R j, v j x) - (48 : ℝ) * ∑ j, μ j
    (∑ j, (μ' j - μ j)) = -E / (6*n : ℕ) := by
  classical
  dsimp only
  have hrem : 6 * (n+8) - 48 = 6*n := by omega
  have hpos : 0 < 6 * (n+8) - 48 := by rw [hrem]; omega
  have hp : ∀ j : ι,
      (∑ x ∈ A j \ R j, v j x) / (6*n : ℕ) -
          (∑ x ∈ A j, v j x) / (6 * (n+8) : ℕ) =
        -((∑ x ∈ R j, v j x) - (48 : ℝ) *
          ((∑ x ∈ A j, v j x) / (6 * (n+8) : ℕ))) / (6*n : ℕ) := by
    intro j
    have h := prefix_remaining_mean_eq (A j) (R j) (v j) (6*(n+8)) 48
      (hR j) (hA j) (hcard j) hpos
    rw [hrem] at h
    rw [h]
    push_cast
    ring
  calc
    _ = ∑ j : ι, -((∑ x ∈ R j, v j x) - (48 : ℝ) *
          ((∑ x ∈ A j, v j x) / (6 * (n+8) : ℕ))) / (6*n : ℕ) := by
      exact Finset.sum_congr rfl (fun j _ => hp j)
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]

/-- The 12-entry-per-stage aggregate recentering cost is exactly `2/n`
times the removed-label discrepancy. This is an aggregate identity, so it
cannot be applied separately to arbitrary line-dependent coefficients. -/
theorem fw_growth_twelve_weight_mean_shift {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (n : ℕ) (hn : 0 < n) (A R : ι → Finset α) (v : ι → α → ℝ)
    (hA : ∀ j, (A j).card = 6 * (n+8))
    (hR : ∀ j, R j ⊆ A j) (hcard : ∀ j, (R j).card = 48) :
    let μ := fun j => (∑ x ∈ A j, v j x) / (6 * (n+8) : ℕ)
    let μ' := fun j => (∑ x ∈ A j \ R j, v j x) / (6*n : ℕ)
    let E := (∑ j, ∑ x ∈ R j, v j x) - (48 : ℝ) * ∑ j, μ j
    |12 * (∑ j, (μ' j - μ j))| = (2 / (n : ℝ)) * |E| := by
  classical
  dsimp only
  rw [fw_growth_remaining_mean_shift n hn A R v hA hR hcard]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hnn : (0 : ℝ) ≤ 2 / (n : ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg n)
  have heq : 12 * (-((∑ j, ∑ x ∈ R j, v j x) - (48 : ℝ) *
      ∑ j, ((∑ x ∈ A j, v j x) / (6 * (n+8) : ℕ))) / (6*n : ℕ)) =
      -(2 / (n : ℝ)) * ((∑ j, ∑ x ∈ R j, v j x) - (48 : ℝ) *
        ∑ j, ((∑ x ∈ A j, v j x) / (6 * (n+8) : ℕ))) := by
    push_cast
    field_simp
    ring
  rw [heq, abs_mul, abs_neg, abs_of_nonneg hnn]


/-- The PD6 selected-discrepancy bound controls the common twelve-entry
aggregate recentering cost by `3*C/n`. Physical row/column incidence must
be proved separately before applying this numerical bound to a line. -/
theorem fw_growth_twelve_weight_mean_shift_bound {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (n : ℕ) (hn : 0 < n) (A R : ι → Finset α) (v : ι → α → ℝ) (C : ℝ)
    (hA : ∀ j, (A j).card = 6 * (n+8))
    (hR : ∀ j, R j ⊆ A j) (hcard : ∀ j, (R j).card = 48)
    (hE : |(∑ j, ∑ x ∈ R j, v j x) - (48 : ℝ) *
      ∑ j, ((∑ x ∈ A j, v j x) / (6*(n+8) : ℕ))| ≤ (3/2:ℝ)*C) :
    |12 * (∑ j, ((∑ x ∈ A j \ R j, v j x) / (6*n : ℕ) -
      (∑ x ∈ A j, v j x) / (6*(n+8) : ℕ)))| ≤ 3*C/(n : ℝ) := by
  classical
  rw [fw_growth_twelve_weight_mean_shift n hn A R v hA hR hcard]
  calc
    _ ≤ (2 / (n : ℝ)) * ((3/2:ℝ)*C) :=
      mul_le_mul_of_nonneg_left hE (div_nonneg (by norm_num) (Nat.cast_nonneg n))
    _ = 3*C/(n : ℝ) := by ring

end
end Sude
