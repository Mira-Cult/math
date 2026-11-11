import Sude.FWPermutationExceptionBound

/-! The FW conditioned small-cut coefficient at the source parameters.
This certifies a real inequality only, not a cut-union or graph existence. -/
namespace Sude

/-- FW's logarithmic small-cut gate with α=173/1000, β=1481/1000,
and the exact split t₀=1/256. All logarithm bounds are proved in Lean. -/
theorem fw_small_cut_gate :
    1 + 3 * Real.binEntropy ((173 : ℝ) / 1000) +
      (1481 / 1000 : ℝ) * Real.log (1 / 256) +
      3 * Real.log 3 < Real.log (1 / 8) := by
  have hlog2 : (69 : ℝ) / 100 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog3 : 5 * Real.log 3 ≤ 8 * Real.log 2 := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 3 ^ 5)
      (by norm_num : (3 : ℝ) ^ 5 ≤ 2 ^ 8)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    linarith
  have hloga : 5 * Real.log ((173 : ℝ) / 1000)⁻¹ ≤ 13 * Real.log 2 := by
    have h := Real.log_le_log
      (by positivity : (0 : ℝ) < (((173 : ℝ) / 1000)⁻¹) ^ 5)
      (by norm_num : (((173 : ℝ) / 1000)⁻¹) ^ 5 ≤ 2 ^ 13)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    linarith
  have hlogb : Real.log (1 - (173 : ℝ) / 1000)⁻¹ ≤ (173 : ℝ) / 827 := by
    have h := Real.log_le_sub_one_of_pos
      (by positivity : 0 < (1 - (173 : ℝ) / 1000)⁻¹)
    norm_num at h ⊢
    exact h
  have hentropy : Real.binEntropy ((173 : ℝ) / 1000) ≤
      (173 : ℝ) / 1000 * (13 / 5 * Real.log 2) + 173 / 1000 := by
    unfold Real.binEntropy
    nlinarith
  have h256 : Real.log ((1 : ℝ) / 256) = -8 * Real.log 2 := by
    have h : (1 : ℝ) / 256 = (2 ^ 8)⁻¹ := by norm_num
    rw [h, Real.log_inv, Real.log_pow]
    norm_num
  have h8 : Real.log ((1 : ℝ) / 8) = -3 * Real.log 2 := by
    have h : (1 : ℝ) / 8 = (2 ^ 3)⁻¹ := by norm_num
    rw [h, Real.log_inv, Real.log_pow]
    norm_num
  rw [h256, h8]
  linarith

end Sude
