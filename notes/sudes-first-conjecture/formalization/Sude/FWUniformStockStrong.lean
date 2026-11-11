import Sude.FWUniformStockFloor
import Sude.FWLogUpper

/-! A stronger rational stock lower bound in the actual FW scale. -/
namespace Sude
noncomputable section

/-- On this real domain, the explicit FW stock is at least `X/3500`.
This only estimates the stock; it does not establish any budget or gate. -/
theorem fw_uniform_real_stock_ge_one_over_3500 (X : ℝ)
    (hX : (2 : ℝ) ^ 32 ≤ X) (hlog_upper : Real.log X ≤ 29) :
    X / 3500 ≤ fwUniformRealStock X := by
  have hX0 : 0 ≤ X := by norm_num at hX ⊢; linarith
  have hXlarge : (4294967296 : ℝ) ≤ X := by norm_num at hX ⊢; exact hX
  have htheta : ((123 / 250 : ℝ) + ((16 / 235 : ℝ) + 1 / 3) + 16 / 235) ≤ 1 := by norm_num
  have hthetaX : ((123 / 250 : ℝ) + ((16 / 235 : ℝ) + 1 / 3) + 16 / 235) * X ≤ X := by nlinarith
  have hsqrtTheta := Real.sqrt_le_sqrt hthetaX
  have hprod : 0 ≤ X * (X - 4294967296) := mul_nonneg hX0 (by linarith)
  have hsqrtX : Real.sqrt X ≤ X / 65536 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  unfold fwUniformRealStock
  apply (le_div_iff₀ hlog).mpr
  nlinarith [mul_nonneg hX0 (sub_nonneg.mpr hlog_upper)]

/-- The stronger bound holds at the actual FW maximum under the stated
Rosser--Schoenfeld index estimates. No actual deletion budget is discharged. -/
theorem fw_poolMaximum_uniform_stock_ge_one_over_3500
    (upper : RSIndexUpper) (lower : RSIndexLower) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    (poolMaximum n : ℝ) / 3500 ≤ fwUniformRealStock (poolMaximum n) := by
  have hXnat : 2 ^ 32 ≤ poolMaximum n := by
    have h := le_of_lt (fw_poolMaximum_gt_four_seed lower hnlo)
    norm_num at h ⊢
    exact h
  have hX : (2 : ℝ) ^ 32 ≤ poolMaximum n := by exact_mod_cast hXnat
  exact fw_uniform_real_stock_ge_one_over_3500 (poolMaximum n) hX
    (le_of_lt (fw_poolMaximum_log_lt_29 upper hnlo hnhi))

end
end Sude
