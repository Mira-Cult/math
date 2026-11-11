import Sude.FWEntropySmallEndpoint

/-! The tight right endpoint of FW's large-cut entropy inequality. -/
namespace Sude
noncomputable section

/-- At the source endpoint `t=1/2`, the FW entropy is below `-1/250`.
The logarithm bounds are derived from mathlib's rational certificates,
a rational logarithm tangent bound, and a finite Taylor remainder; this
single endpoint alone does not prove FW's interval or expander. -/
theorem fw_entropy_half_endpoint : fwCutEntropy (1 / 2) < -(1 : ℝ) / 250 := by
  have hlog2lo : (6931471803 : ℝ) / 10000000000 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log 2 < (6931471808 : ℝ) / 10000000000 := by
    linarith [Real.log_two_lt_d9]
  have hlog3hi : Real.log 3 < (10986122888 : ℝ) / 10000000000 := by
    linarith [Real.log_three_lt_d9]
  have hlog519 : (38 / 1019 : ℝ) ≤ Real.log (519 / 500) := by
    have h := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 19 / 500 by norm_num)
    norm_num at h ⊢
    exact h
  have hloga : Real.log ((173 : ℝ) / 1000)⁻¹ ≤
      Real.log 2 + Real.log 3 - 38 / 1019 := by
    have hfactor : ((173 : ℝ) / 1000)⁻¹ = (2 * 3) / (519 / 500) := by norm_num
    rw [hfactor, Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hlogb : Real.log (1 - (173 : ℝ) / 1000)⁻¹ ≤ (19 : ℝ) / 100 := by
    have h := Real.abs_log_sub_add_sum_range_le
      (x := (173 : ℝ) / 1000) (by norm_num) 5
    have hlow := (abs_le.mp h).1
    rw [Real.log_inv]
    norm_num [Finset.sum_range_succ] at hlow ⊢
    linarith
  have hentropy : Real.binEntropy ((173 : ℝ) / 1000) ≤
      (173 : ℝ) / 1000 * (Real.log 2 + Real.log 3 - 38 / 1019) +
        (827 / 1000) * (19 / 100) := by
    unfold Real.binEntropy
    nlinarith
  have hhalf : Real.binEntropy ((1 : ℝ) / 2) = Real.log 2 := by
    simpa only [one_div] using Real.binEntropy_two_inv
  unfold fwCutEntropy
  have heq : ((173 : ℝ) / 1000) * (1 / 2) / (1 - 1 / 2) = 173 / 1000 := by norm_num
  rw [heq, hhalf]
  linarith

end
end Sude
