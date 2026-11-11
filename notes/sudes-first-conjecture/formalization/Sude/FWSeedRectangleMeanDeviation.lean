import Sude.FWSeedGlobalRectangleLines
/-! Bounds for supplied mean deviations on actual seed rectangles.
No mean bound or full-line estimate is asserted. -/
namespace Sude
noncomputable section

private theorem weighted_bound {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (w d : α → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hw : ∀ i, 0 ≤ w i) (hsum : (∑ i, w i) ≤ 2)
    (hd : ∀ i ∈ s, |d i| ≤ β) :
    |∑ i ∈ s, d i * w i| ≤ 2 * β := by
  have hsub : s ⊆ Finset.univ := Finset.subset_univ _
  have hsum' : (∑ i ∈ s, w i) ≤ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro i _ _; exact hw i)).trans hsum
  calc
    |∑ i ∈ s, d i * w i| ≤ ∑ i ∈ s, |d i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, β * w i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i)]
      exact mul_le_mul_of_nonneg_right (hd i hi) (hw i)
    _ = β * ∑ i ∈ s, w i := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * β := by nlinarith

theorem fw_seed_row_rectangle_weighted_deviation_bound {n L : ℕ}
    (hseed : 5 * (4*6) + 16 * (4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (s : Finset (Fin 16)) (r : Fin n)
    (μs : Fin 16 → ℝ) (μ β : ℝ) (hβ : 0 ≤ β)
    (hd : ∀ j ∈ s, |μs j - μ| ≤ β) :
    |∑ j ∈ s, (μs j - μ) * fwSeedRectangleStageLineWeight hseed hs choice (fun c => c.1 = r) j| ≤ 2 * β := by
  classical
  apply weighted_bound s _ (fun j => μs j - μ) β hβ
  · intro j
    rw [fw_seed_rectangle_row_stage_weight]
    split_ifs <;> norm_num
  · have h := fw_seed_global_row_rectangle_indicator hseed hs choice r
    change (∑ j, fwSeedRectangleStageLineWeight hseed hs choice (fun c => c.1 = r) j) = _ at h
    rw [h]
    split_ifs <;> norm_num
  · exact hd

theorem fw_seed_column_rectangle_weighted_deviation_bound {n L : ℕ}
    (hseed : 5 * (4*6) + 16 * (4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (s : Finset (Fin 16)) (c : Fin n)
    (μs : Fin 16 → ℝ) (μ β : ℝ) (hβ : 0 ≤ β)
    (hd : ∀ j ∈ s, |μs j - μ| ≤ β) :
    |∑ j ∈ s, (μs j - μ) * fwSeedRectangleStageLineWeight hseed hs choice (fun x => x.2 = c) j| ≤ 2 * β := by
  classical
  apply weighted_bound s _ (fun j => μs j - μ) β hβ
  · intro j
    rw [fw_seed_rectangle_column_stage_weight]
    split_ifs <;> norm_num
  · have h := fw_seed_global_column_rectangle_indicator hseed hs choice c
    change (∑ j, fwSeedRectangleStageLineWeight hseed hs choice (fun x => x.2 = c) j) = _ at h
    rw [h]
    split_ifs <;> norm_num
  · exact hd
end
end Sude
