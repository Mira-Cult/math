import Sude.FWFirstBandTargetSpread
import Sude.FWPoolBound

/-! Direct finite BMOR theta inputs do not reach the first-band nominal
T75 target window. This does not rule out prime supply or the separate
general-character progression argument. -/
namespace Sude
noncomputable section

/-- The actual nominal lower endpoint exceeds the largest finite cutoff. -/
theorem fw_t75_nominal_lower_above_finite_bmor
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    let y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
    (4 * 10^13 : ℝ) < y - y / 1240 := by
  dsimp only
  let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  have hn : (19485 : ℝ) ≤ n := by exact_mod_cast hnlo
  have hX : (4 * 2^30 : ℝ) < poolMaximum n := by
    exact_mod_cast fw_poolMaximum_gt_four_seed lower hnlo
  have hm := (fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo (by omega)).1
  rw [← prescribedPoolValues_mean] at hm
  have hm' : (243 / 500 : ℝ) * (4 * 2^30 : ℝ) < μ := by
    dsimp [μ]
    nlinarith
  have hprod := mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) - 19485 by linarith)
    (show (0 : ℝ) ≤ μ - (243 / 500 : ℝ) * (4 * 2^30 : ℝ) by linarith)
  change (4 * 10^13 : ℝ) < (n : ℝ)*μ - (n : ℝ)*μ/1240
  norm_num at hprod ⊢
  nlinarith

/-- Every encoded finite BMOR limit is at most 4·10¹³. -/
theorem bmor_finite_limit_le_four_ten_pow_thirteen (q : ℕ) :
    bmorLimit q ≤ 4 * 10 ^ 13 := by
  unfold bmorLimit bmorBaseLimit
  split_ifs <;> norm_num

/-- No point at or above the nominal lower endpoint lies in that finite domain. -/
theorem fw_t75_nominal_point_above_finite_bmor
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (q : ℕ) (z : ℝ)
    (hz : (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue -
      ((n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue) / 1240 ≤ z) :
    (bmorLimit q : ℝ) < z := by
  have hlim : (bmorLimit q : ℝ) ≤ 4 * 10 ^ 13 := by
    exact_mod_cast bmor_finite_limit_le_four_ten_pow_thirteen q
  have hwin := fw_t75_nominal_lower_above_finite_bmor bmor lower upper hnlo hnhi
  linarith

end
end Sude

