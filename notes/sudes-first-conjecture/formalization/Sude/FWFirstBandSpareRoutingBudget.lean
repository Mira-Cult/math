import Sude.FWFirstBandCYRoutingBudget
import Sude.FWFirstBandTargetSpread

/-! First-band scalar routing slack for a supplied extra `X` line error.
No spare-cell balancing, physical square modification, prime supply, or
flow realization is asserted here. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The nominal T75 spread is strictly below `9X` under the stated finite
theta and Rosser--Schoenfeld hypotheses on the first FW band. -/
theorem fw_first_band_nominal_spread_lt_nine
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) :
    (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240 <
      9 * (poolMaximum n : ℝ) := by
  rw [prescribedPoolValues_mean]
  have hmean := (fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo (by omega)).2
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hn : (n : ℝ) ≤ 21248 := by exact_mod_cast hnhi
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hm := mul_le_mul_of_nonneg_left hmean hn0
  have hnx := mul_le_mul_of_nonneg_right hn hX.le
  nlinarith

/-- If a separately established line perturbation costs at most `X` and
the supplied spread is at most `9X`, the enlarged radius satisfies the
strict first-band routing budget. -/
theorem fw_first_band_cy_routing_budget_with_spare_perturbation
    (lower : RSIndexLower) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (D : ℝ) (hD : D ≤ 9 * (poolMaximum n : ℝ)) :
    fwFrozenCYLineRadius n + (poolMaximum n : ℝ) + D <
      (518481/500000 : ℝ) * (((n/450)*poolMaximum n : ℕ) : ℝ) := by
  have hXpos : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hX : (0 : ℝ) ≤ poolMaximum n := hXpos.le
  have hq : 43 ≤ n/450 := by omega
  have hqR : (43 : ℝ) ≤ ((n/450 : ℕ) : ℝ) := by exact_mod_cast hq
  have hmul := mul_nonneg (show 0 ≤ ((n/450 : ℕ) : ℝ) - 43 by linarith) hX
  have hline := fw_frozen_cy_line_radius_le_34 lower hnlo hnhi
  push_cast
  nlinarith

/-- Specialize the enlarged scalar budget to the nominal T75 spread across `19485 ≤ n ≤ 35733`. -/
theorem fw_first_band_nominal_routing_budget_with_spare_perturbation
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    fwFrozenCYLineRadius n + (poolMaximum n : ℝ) +
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240 <
      (518481/500000 : ℝ) * (((n/450)*poolMaximum n : ℕ) : ℝ) := by
  by_cases h21 : n ≤ 21248
  · exact fw_first_band_cy_routing_budget_with_spare_perturbation lower hnlo h21 _
      (le_of_lt (fw_first_band_nominal_spread_lt_nine bmor lower upper hnlo h21))
  · rw [prescribedPoolValues_mean]
    have hmean := (fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo hnhi).2
    have hXpos : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
    have hX : (0 : ℝ) ≤ poolMaximum n := hXpos.le
    have hq : 47 ≤ n / 450 := by omega
    have hqR : (47 : ℝ) ≤ ((n / 450 : ℕ) : ℝ) := by exact_mod_cast hq
    have hmod : n ≤ 450 * (n / 450) + 449 := by
      have := Nat.div_add_mod n 450
      have := Nat.mod_lt n (by decide : 0 < 450)
      omega
    have hmodR : (n : ℝ) ≤ 450 * ((n / 450 : ℕ) : ℝ) + 449 := by exact_mod_cast hmod
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left hmean hn0
    have hnx := mul_le_mul_of_nonneg_right hmodR hX
    have hmul := mul_nonneg (show 0 ≤ ((n / 450 : ℕ) : ℝ) - 47 by linarith) hX
    have hline := fw_frozen_cy_line_radius_le_36 lower hnlo hnhi
    push_cast at hm ⊢
    nlinarith

end
end Sude
