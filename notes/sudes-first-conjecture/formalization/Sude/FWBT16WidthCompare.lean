import Sude.FWBT16LowerGrowth
import Sude.FWFirstBandFullStockSlack

/-! Compare the actual varying-stock BT width to the conservative fixed-floor
width. This is a conditional trace comparison, not a stage construction. -/
namespace Sude
noncomputable section

/-- BT16 width for the source's varying normalized stock at global index j. -/
def fwBT16VaryingWidth (j R : ℕ) : ℝ :=
  8 * ((3981035 / 10000000 : ℝ) * fwFirstBandMu j * R - 1 / 2)

/-- At every eligible global stage the varying-stock width dominates the
fixed-floor width used by the ten-stage recurrence. -/
theorem fw_bt16_fixed_width_le_varying {j R : ℕ} (hj : j ≤ 238) :
    fwBT16FixedWidth R ≤ fwBT16VaryingWidth j R := by
  have hm := (fw_first_band_full_stock_quota_slack hj).1
  have hR : (0 : ℝ) ≤ R := by positivity
  have hmul := mul_le_mul_of_nonneg_right hm hR
  unfold fwBT16FixedWidth fwBT16VaryingWidth
  nlinarith

/-- A variable-stock trace through global stage 238 also satisfies the fixed
width trace at any output index. Actual radii and stages are unchanged. -/
theorem fw_bt16_varying_width_trace_fixed {j R : ℕ} {stages : List BTSelectedStage}
    (widths : BTWidthTrace fwBT16VaryingWidth j R stages)
    (hcap : j + stages.length ≤ 239) (outIndex : ℕ) :
    BTWidthTrace (fun _ r => fwBT16FixedWidth r) outIndex R stages := by
  induction widths generalizing outIndex with
  | nil j R => exact BTWidthTrace.nil outIndex R
  | cons j R stage tail hwidth hrest ih =>
    have hj : j ≤ 238 := by simp only [List.length_cons] at hcap; omega
    have hfixed := (fw_bt16_fixed_width_le_varying (j := j) (R := R) hj).trans hwidth
    apply BTWidthTrace.cons outIndex R stage tail hfixed
    apply ih (by simp only [List.length_cons] at hcap; omega) (outIndex + 1)

end
end Sude
