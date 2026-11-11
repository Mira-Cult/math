import Sude.FWFirstBandTargetSpread
import Sude.CenteredGrid

/-! A scalar obstruction to the window-wide repair gate for a radius with
the new crossing-trace upper bound. This makes no assertion about the earlier
capacity selector or the existence of a prime-line square. -/
namespace Sude
noncomputable section

/-- A supplied radius no larger than the constructed crossing-trace bound has
less than the nominal T75 window width at its even-grid center. -/
theorem fw_bounded_crossing_center_lt_nominal_spread
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n R : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (hR : (R : ℝ) ≤ max (32 : ℝ) (2 * ((poolMaximum n : ℝ) / 23))) :
    (evenGridCenter R : ℝ) <
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240 := by
  rw [prescribedPoolValues_mean]
  have hmean := (fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo (by omega)).1
  have hXnat : 100 ≤ poolMaximum n := by
    have h := fw_poolMaximum_gt_four_seed lower hnlo
    omega
  have hX : (100 : ℝ) ≤ poolMaximum n := by exact_mod_cast hXnat
  have hn : (19485 : ℝ) ≤ n := by exact_mod_cast hnlo
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hm := mul_le_mul_of_nonneg_left hmean hn0
  have hnx := mul_le_mul_of_nonneg_right hn (show (0 : ℝ) ≤ poolMaximum n by positivity)
  have hbig : 7 * (poolMaximum n : ℝ) <
      (n : ℝ) * ((Lucas.poolTotal n : ℝ) / (n * n : ℕ)) / 1240 := by
    nlinarith
  have h32 : (32 : ℝ) < 2 * ((n : ℝ) * ((Lucas.poolTotal n : ℝ) / (n * n : ℕ)) / 1240) := by
    nlinarith
  have h2 : 2 * ((poolMaximum n : ℝ) / 23) <
      2 * ((n : ℝ) * ((Lucas.poolTotal n : ℝ) / (n * n : ℕ)) / 1240) := by
    nlinarith
  have hcenter : 2 * (evenGridCenter R : ℝ) ≤ R := by
    exact_mod_cast evenGridCenter_twice_le R
  have hmax := max_lt h32 h2
  nlinarith

/-- For such a radius no nonnegative-error window-wide gate can hold, even
for one supplied reference sum. -/
theorem fw_bounded_crossing_window_gate_impossible
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n R : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (hR : (R : ℝ) ≤ max (32 : ℝ) (2 * ((poolMaximum n : ℝ) / 23)))
    (reference U : ℝ)
    (herror : |reference - (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ U) :
    ¬ U + (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240 ≤
      (evenGridCenter R : ℝ) := by
  have hlt := fw_bounded_crossing_center_lt_nominal_spread bmor lower upper hnlo hnhi hR
  have hU : 0 ≤ U := (abs_nonneg _).trans herror
  linarith

end
end Sude
