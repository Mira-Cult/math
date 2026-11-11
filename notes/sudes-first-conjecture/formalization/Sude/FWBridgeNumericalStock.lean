import Sude.FWBridgeWindowDisjoint

/-! Uniform real FW bridge stock on the five nominal source stages. -/
namespace Sude
noncomputable section

/-- Each of the five source windows has width between the first-stage
width and the final capped-stage width. -/
theorem fw_bridge_nominal_width_bounds (X : ℝ) (hX : 0 < X)
    (j : ℕ) (hj : j < 5) :
    X / 462 ≤ fwBridgeWidth X (fwBridgeRadius X j) ∧
      fwBridgeWidth X (fwBridgeRadius X j) ≤ (23 / 924 : ℝ) * X := by
  have hmin : (1 / 23 : ℝ) ≤ min (fwBridgeRatio j) (1 / 2) := by
    interval_cases j <;> norm_num [fwBridgeRatio]
  have hmax : min (fwBridgeRatio j) (1 / 2) ≤ (1 / 2 : ℝ) := min_le_right _ _
  have hscale := fw_bridge_nominal_span_scale X hX j
  simp only [fwBridgeWidth, hscale]
  constructor <;> nlinarith

/-- The common BMOR stock expression is at least `X/15000` on each of
the five nominal stages. The assumptions are real numerical bounds; this
statement does not by itself establish any prime-count or selection gate. -/
theorem fw_bridge_nominal_stock_bound_ge_linear (X : ℝ)
    (hX : (2 : ℝ) ^ 32 ≤ X) (hlog : Real.log X ≤ 29)
    (j : ℕ) (hj : j < 5) :
    X / 15000 ≤ fwBridgeStockBound X (fwBridgeRadius X j) := by
  have hX0 : 0 ≤ X := by norm_num at hX; linarith
  have hXpos : 0 < X := by norm_num at hX; linarith
  have hsqrtArg : 3 * X / 4 ≤ X := by linarith
  have hsqrtTheta := Real.sqrt_le_sqrt hsqrtArg
  have hprod : 0 ≤ X * (X - 4294967296) := mul_nonneg hX0 (by norm_num at hX; linarith)
  have hsqrt : Real.sqrt X ≤ X / 65536 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hwidth := (fw_bridge_nominal_width_bounds X hXpos j hj).1
  have hlogpos : 0 < Real.log X := Real.log_pos (by norm_num at hX; linarith)
  have hlogprod : 0 ≤ X * (29 - Real.log X) := mul_nonneg hX0 (by linarith)
  unfold fwBridgeStockBound
  apply (le_div_iff₀ hlogpos).mpr
  nlinarith

end
end Sude
