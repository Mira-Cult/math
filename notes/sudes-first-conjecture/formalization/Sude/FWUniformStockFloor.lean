import Sude.FWReflectedStockGate
import Mathlib.Algebra.Order.Floor.Defs

/-! A concrete integer stock from FW's explicit midpoint estimate. -/
namespace Sude
noncomputable section

/-- The source-style uniform midpoint-error stock lower bound. -/
def fwUniformRealStock (X : ℝ) : ℝ :=
  ((2 / 235 : ℝ) * X - 2 * (518 / 125 : ℝ) *
    Real.sqrt (((123 / 250 : ℝ) + ((16 / 235 : ℝ) + 1 / 3) + 16 / 235) * X)) /
      Real.log X

/-- An exact natural stock count, rounded down. -/
def fwUniformNaturalStock (X : ℝ) : ℕ := ⌊fwUniformRealStock X⌋₊

/-- The uniform real stock expression is positive for every `X ≥ 10^8`.
The proof uses rational bounds and the defining inequality for square root. -/
theorem fw_uniform_real_stock_pos (X : ℝ) (hX : 100000000 ≤ X) :
    0 < fwUniformRealStock X := by
  have hX0 : 0 ≤ X := by linarith
  have htheta : (0 : ℝ) ≤ (123 / 250 : ℝ) + ((16 / 235 : ℝ) + 1 / 3) + 16 / 235 := by norm_num
  have hthetale : ((123 / 250 : ℝ) + ((16 / 235 : ℝ) + 1 / 3) + 16 / 235) ≤ 1 := by norm_num
  have hthetaX : ((123 / 250 : ℝ) + ((16 / 235 : ℝ) + 1 / 3) + 16 / 235) * X ≤ X := by nlinarith
  have hsqrtTheta := Real.sqrt_le_sqrt hthetaX
  have hprod : 0 ≤ X * (X - 100000000) := mul_nonneg hX0 (by linarith)
  have hsqrtX : Real.sqrt X ≤ X / 10000 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hnum : 0 < (2 / 235 : ℝ) * X - 2 * (518 / 125 : ℝ) *
      Real.sqrt (((123 / 250 : ℝ) + ((16 / 235 : ℝ) + 1 / 3) + 16 / 235) * X) := by
    nlinarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  exact div_pos hnum hlog

/-- The rounded natural stock does not exceed the explicit real bound. -/
theorem fw_uniform_natural_stock_le (X : ℝ) (hX : 100000000 ≤ X) :
    (fwUniformNaturalStock X : ℝ) ≤ fwUniformRealStock X := by
  exact Nat.floor_le (fw_uniform_real_stock_pos X hX).le

end
end Sude
