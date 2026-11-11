import Sude.FWPoolBound
import Sude.FWFirstBandLogScoreBounds
import Mathlib.Tactic

/-! An exact first-band upper bound for the finite-seed allocation radius.
This proves no seed supply, target existence, or complete-line estimate. -/
namespace Sude
noncomputable section

/-- The actual seed concentration term is at most `3X/2`, where
`X = poolMaximum n`. -/
theorem fw_first_band_seed_radius_le_three_halves
    (lower : RSIndexLower) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    Real.sqrt (((11/2 : ℝ) * ((2^30 : ℕ) : ℝ)^2) *
      Real.log (4 * (((n+n)+2 : ℕ) : ℝ)) / 2) ≤
      (3/2 : ℝ) * poolMaximum n := by
  let L : ℝ := 4 * (((n+n)+2 : ℕ) : ℝ)
  let S : ℝ := ((2^30 : ℕ) : ℝ)
  have hlogBound : Real.log L ≤ 13 := by
    have hL : L = 8 * (n : ℝ) + 8 := by dsimp [L]; push_cast; ring
    rw [hL]
    exact fw_first_band_log_eight_le_thirteen hnhi
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hsqrt : Real.sqrt (((11/2 : ℝ) * S^2) * Real.log L / 2) ≤ 6*S := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hm := mul_nonneg (show 0 ≤ 13 - Real.log L by linarith) (sq_nonneg S)
      nlinarith
  have hXnat := fw_poolMaximum_gt_four_seed lower hnlo
  have hX : 4*S < (poolMaximum n : ℝ) := by
    dsimp [S]
    exact_mod_cast hXnat
  have hfinish : 6*S ≤ (3/2 : ℝ) * poolMaximum n := by
    calc
      6*S = (3/2 : ℝ)*(4*S) := by ring
      _ ≤ (3/2 : ℝ) * poolMaximum n :=
        mul_le_mul_of_nonneg_left (le_of_lt hX) (by norm_num)
  simpa only [L, S] using hsqrt.trans hfinish

end
end Sude
