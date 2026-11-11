import Sude.FC2KBridge

/-! Source-faithful FW/BB bridge geometry.

The width `23/462`, initial normalized radius `1/23`, five stage spans,
and resulting coverage are the fixed FW bridge profile in
`problems/prime-line-sums/inputs/cutoff2_controller_far_wide_inputs.json`,
`bands[*].gaps["2"].geometry`, and the selection order is described in
`problems/prime-line-sums/manuscripts/cutoff2_controller_far_wide.md` FW2--FW4.
These definitions do not replace FC2K's separately stated `3/100` windows.
-/
namespace Sude
noncomputable section

/-- FW's actual bridge width and its reflected half-open windows. -/
def fwBridgeWidth (X R : ℝ) : ℝ := (23 / 462 : ℝ) * bridgeSpan X R

def fwBridgeLowStart (X R : ℝ) : ℝ := X / 2 - bridgeSpan X R / 2
def fwBridgeLowEnd (X R : ℝ) : ℝ := fwBridgeLowStart X R + fwBridgeWidth X R
def fwBridgeHighEnd (X R : ℝ) : ℝ := X / 2 + bridgeSpan X R / 2
def fwBridgeHighStart (X R : ℝ) : ℝ := fwBridgeHighEnd X R - fwBridgeWidth X R

def fwBridgeGapLower (X R : ℝ) : ℝ := bridgeSpan X R - 2 * fwBridgeWidth X R

/-- The width and gap use exactly the source's rational coefficients. -/
theorem fw_bridge_width_and_increment (X R : ℝ) :
    fwBridgeWidth X R = (23 / 462 : ℝ) * bridgeSpan X R ∧
    fwBridgeGapLower X R = (208 / 231 : ℝ) * bridgeSpan X R := by
  constructor
  · rfl
  · simp only [fwBridgeGapLower, fwBridgeWidth]
    ring

/-- FW's two windows lie in `[X/4,3X/4]`, have the specified common
width, and are strictly separated. Endpoints describe `(start,end]` windows. -/
theorem fw_bridge_window_geometry (X R : ℝ) (hX : 0 < X) (hR : 0 < R) :
    0 < fwBridgeWidth X R ∧ 0 < fwBridgeGapLower X R ∧
    X / 4 ≤ fwBridgeLowStart X R ∧
    fwBridgeLowStart X R < fwBridgeLowEnd X R ∧
    fwBridgeLowEnd X R < fwBridgeHighStart X R ∧
    fwBridgeHighStart X R < fwBridgeHighEnd X R ∧
    fwBridgeHighEnd X R ≤ 3 * X / 4 ∧
    fwBridgeLowEnd X R - fwBridgeLowStart X R = fwBridgeWidth X R ∧
    fwBridgeHighEnd X R - fwBridgeHighStart X R = fwBridgeWidth X R := by
  have hs := bridgeSpan_properties X R hX hR
  simp only [fwBridgeWidth, fwBridgeGapLower, fwBridgeLowStart, fwBridgeLowEnd,
    fwBridgeHighStart, fwBridgeHighEnd]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [hs.1, hs.2.2]

/-- A low/high pair in the source windows has the strict source gap bounds.
The order is established before casting the natural subtraction. -/
theorem fw_bridge_cross_gap (X R : ℝ) (hX : 0 < X) (hR : 0 < R) (a b : ℕ)
    (ha : fwBridgeLowStart X R < (a : ℝ) ∧ (a : ℝ) ≤ fwBridgeLowEnd X R)
    (hb : fwBridgeHighStart X R < (b : ℝ) ∧ (b : ℝ) ≤ fwBridgeHighEnd X R) :
    a < b ∧ 0 < b - a ∧
      fwBridgeGapLower X R < ((b - a : ℕ) : ℝ) ∧
      ((b - a : ℕ) : ℝ) < bridgeSpan X R ∧
      ((b - a : ℕ) : ℝ) ≤ R := by
  have hg := fw_bridge_window_geometry X R hX hR
  have hs := bridgeSpan_properties X R hX hR
  have habReal : (a : ℝ) < b := by linarith [hg.2.2.2.2.1]
  have hab : a < b := by exact_mod_cast habReal
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := Nat.cast_sub (le_of_lt hab)
  refine ⟨hab, by omega, ?_, ?_, ?_⟩ <;>
    rw [hcast] <;>
    simp only [fwBridgeGapLower, fwBridgeWidth, fwBridgeLowStart, fwBridgeLowEnd,
      fwBridgeHighStart, fwBridgeHighEnd] at * <;> linarith [hs.2.1]

/-- For actual pool endpoints the above positive gap is even. -/
theorem fw_bridge_pool_gap_even {n a b : ℕ} (X R : ℝ) (hX : 0 < X) (hR : 0 < R)
    (haPool : a ∈ pool n) (hbPool : b ∈ pool n)
    (ha : fwBridgeLowStart X R < (a : ℝ) ∧ (a : ℝ) ≤ fwBridgeLowEnd X R)
    (hb : fwBridgeHighStart X R < (b : ℝ) ∧ (b : ℝ) ≤ fwBridgeHighEnd X R) :
    2 ∣ b - a := by
  exact pool_ordered_difference_even haPool hbPool
    (le_of_lt (fw_bridge_cross_gap X R hX hR a b ha hb).1)

/-- Nominal lower coverage, normalized by X. It is not the actual chosen
grid radius; each stage uses its capped span `min(radius,1/2)`. -/
def fwBridgeRatio : ℕ → ℝ
  | 0 => 1 / 23
  | j + 1 => fwBridgeRatio j + (208 / 231 : ℝ) * min (fwBridgeRatio j) (1 / 2)

def fwBridgeRadius (X : ℝ) (j : ℕ) : ℝ := fwBridgeRatio j * X

/-- Scaling the normalized recurrence gives exactly the width-dependent
bridge increment for every positive X. -/
theorem fw_bridge_radius_succ (X : ℝ) (hX : 0 < X) (j : ℕ) :
    fwBridgeRadius X (j + 1) = fwBridgeRadius X j + fwBridgeGapLower X (fwBridgeRadius X j) := by
  have hspan : bridgeSpan X (fwBridgeRadius X j) =
      min (fwBridgeRatio j) (1 / 2) * X := by
    rw [min_mul_of_nonneg _ _ (le_of_lt hX)]
    simp only [bridgeSpan, fwBridgeRadius]
    congr 1 <;> ring
  rw [(fw_bridge_width_and_increment X (fwBridgeRadius X j)).2, hspan]
  simp only [fwBridgeRadius, fwBridgeRatio]
  ring

/-- Exact five-stage source schedule. The stage-four window span is capped
at `1/2`, although its accumulated lower coverage exceeds `1/2`. -/
theorem fw_bridge_five_stage_schedule :
    fwBridgeRatio 0 = 1 / 23 ∧
    fwBridgeRatio 1 = 439 / 5313 ∧
    fwBridgeRatio 2 = 192721 / 1227303 ∧
    fwBridgeRatio 3 = 84604519 / 283506993 ∧
    fwBridgeRatio 4 = 37141383841 / 65490115383 ∧
    fwBridgeRatio 5 = 66626111113 / 65490115383 ∧
    (∀ j < 5, 0 < fwBridgeRatio j ∧ fwBridgeRatio j < 1) ∧
    min (fwBridgeRatio 4) (1 / 2) = 1 / 2 ∧
    1 < fwBridgeRatio 5 := by
  have hs : ∀ j < 5, 0 < fwBridgeRatio j ∧ fwBridgeRatio j < 1 := by
    intro j hj
    interval_cases j <;> norm_num [fwBridgeRatio]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hs, ?_, ?_⟩ <;> norm_num [fwBridgeRatio]

end
end Sude
