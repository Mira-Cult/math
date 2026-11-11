import Sude.FWUniformStockFloor
import Sude.FWLogUpper

/-! An explicit rational lower bound for FW's uniform real stock. -/
namespace Sude
noncomputable section

/-- On the stated real domain, the FW stock is at least `X/4000`.
This is a numerical stock estimate, not a deletion-budget or square gate. -/
theorem fw_uniform_real_stock_ge_linear (X : ℝ)
    (hX : 100000000 ≤ X) (hlog_upper : Real.log X ≤ 29) :
    X / 4000 ≤ fwUniformRealStock X := by
  have hX0 : 0 ≤ X := by linarith
  have htheta : ((123 / 250 : ℝ) + ((16 / 235 : ℝ) + 1 / 3) + 16 / 235) ≤ 1 := by norm_num
  have hthetaX : ((123 / 250 : ℝ) + ((16 / 235 : ℝ) + 1 / 3) + 16 / 235) * X ≤ X := by nlinarith
  have hsqrtTheta := Real.sqrt_le_sqrt hthetaX
  have hprod : 0 ≤ X * (X - 100000000) := mul_nonneg hX0 (by linarith)
  have hsqrtX : Real.sqrt X ≤ X / 10000 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  unfold fwUniformRealStock
  apply (le_div_iff₀ hlog).mpr
  nlinarith [mul_nonneg hX0 (sub_nonneg.mpr hlog_upper)]

/-- The same bound for the actual FW maximum under the explicit RS index
estimates. The mean, deletion budget and rounded square gate remain open. -/
theorem fw_poolMaximum_uniform_stock_ge_linear
    (upper : RSIndexUpper) (lower : RSIndexLower) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    (poolMaximum n : ℝ) / 4000 ≤ fwUniformRealStock (poolMaximum n) := by
  have hXnat : 100000000 ≤ poolMaximum n :=
    (by decide : 100000000 ≤ 4 * 2 ^ 30).trans (le_of_lt (fw_poolMaximum_gt_four_seed lower hnlo))
  have hX : (100000000 : ℝ) ≤ poolMaximum n := by exact_mod_cast hXnat
  exact fw_uniform_real_stock_ge_linear (poolMaximum n) hX
    (le_of_lt (fw_poolMaximum_log_lt_29 upper hnlo hnhi))

end
end Sude
