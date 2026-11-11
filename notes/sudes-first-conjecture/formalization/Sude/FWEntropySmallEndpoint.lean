import Sude.FC2KExpansionGate

/-! One exact FW graph entropy endpoint, with rational logarithm bounds. -/
namespace Sude
noncomputable section

/-- The large-cut entropy expression for FW's `κ=519/500` and degree 6,
so `α=κ/6=173/1000`. This is only the displayed analytic expression,
not an expander existence assertion. -/
def fwCutEntropy (t : ℝ) : ℝ :=
  3 * (t * Real.binEntropy ((173 : ℝ) / 1000) +
    (1 - t) * Real.binEntropy (((173 : ℝ) / 1000) * t / (1 - t))) -
      2 * Real.binEntropy t

/-- The FW large-cut entropy at the source's left endpoint `t=1/256`
is less than `-1/250`. The logarithm enclosures below are proved in Lean;
this one endpoint does not imply the interval bound or an expander. -/
theorem fw_entropy_small_endpoint : fwCutEntropy (1 / 256) < -(1 : ℝ) / 250 := by
  have hlog2lo : (6931471803 : ℝ) / 10000000000 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log 2 < (6931471808 : ℝ) / 10000000000 := by
    linarith [Real.log_two_lt_d9]
  have hlog3hi : Real.log 3 < (10986122888 : ℝ) / 10000000000 := by
    linarith [Real.log_three_lt_d9]
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
  have hHa : Real.binEntropy ((173 : ℝ) / 1000) ≤
      (173 : ℝ) / 1000 * (13 / 5 * Real.log 2) + 173 / 1000 := by
    unfold Real.binEntropy
    nlinarith
  have h1536 : Real.log (1536 : ℝ) = Real.log 3 + 9 * Real.log 2 := by
    have h : (1536 : ℝ) = 3 * 2 ^ 9 := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hzlog : Real.log ((173 : ℝ) / 255000)⁻¹ ≤
      9 * Real.log 2 + Real.log 3 := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((173 : ℝ) / 255000)⁻¹)
      (by norm_num : ((173 : ℝ) / 255000)⁻¹ ≤ 1536)
    linarith
  have hzother : Real.log (1 - (173 : ℝ) / 255000)⁻¹ ≤
      (173 : ℝ) / 254827 := by
    have h := Real.log_le_sub_one_of_pos
      (by positivity : 0 < (1 - (173 : ℝ) / 255000)⁻¹)
    norm_num at h ⊢
    exact h
  have hHz : Real.binEntropy ((173 : ℝ) / 255000) ≤
      (173 : ℝ) / 255000 * (9 * Real.log 2 + Real.log 3) +
        173 / 255000 := by
    unfold Real.binEntropy
    nlinarith
  have htother : (1 : ℝ) / 256 ≤ Real.log (1 - (1 : ℝ) / 256)⁻¹ := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < 1 - (1 : ℝ) / 256)
    rw [Real.log_inv]
    linarith
  have htlog : Real.log ((1 : ℝ) / 256)⁻¹ = 8 * Real.log 2 := by
    have h : ((1 : ℝ) / 256)⁻¹ = 2 ^ 8 := by norm_num
    rw [h, Real.log_pow]
    norm_num
  have hHt : (1 : ℝ) / 256 * (8 * Real.log 2) +
      (255 / 256) * (1 / 256) ≤ Real.binEntropy (1 / 256) := by
    unfold Real.binEntropy
    rw [htlog]
    nlinarith
  unfold fwCutEntropy
  have heq : ((173 : ℝ) / 1000) * (1 / 256) / (1 - 1 / 256) = 173 / 255000 := by norm_num
  rw [heq]
  linarith

end
end Sude
