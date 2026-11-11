import Sude.FWProjectedCYPrimeTargets
import Sude.FWGrowthFirstBandMidpointGate
import Sude.FWFirstBandLogScoreBounds
import Sude.FWFirstBandSeedRadiusBound
import Sude.FWPoolBound

/-! A conservative first-band FW18 routing budget for the actual frozen CY
line radius. Target existence and the target-spread bound remain separate. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The proved frozen CY line radius is bounded by `34 * poolMaximum n`.
Its local rectangle term and global reservation-cancellation term occur
once each, exactly as in the existing physical line theorem. -/
theorem fw_frozen_cy_line_radius_le_34
    (lower : RSIndexLower) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) :
    fwFrozenCYLineRadius n ≤ (34 : ℝ) * poolMaximum n := by
  let X : ℝ := poolMaximum n
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hXlarge : 4 * (2^30 : ℝ) < X := by
    dsimp [X]
    exact_mod_cast fw_poolMaximum_gt_four_seed lower hnlo
  have hconst : (9/2 : ℝ) ≤ X/100 := by norm_num at hXlarge ⊢; linarith
  have hB := fw_first_band_bridge_sqrt_le_35 (by omega : n ≤ 35733)
  have hW := fw_first_band_wide_sqrt_le_183 hnhi
  have hB' := mul_le_mul_of_nonneg_left hB (show 0 ≤ X * (23/924 : ℝ) by positivity)
  have hW' := mul_le_mul_of_nonneg_left hW (show 0 ≤ X * (2/235 : ℝ) by positivity)
  have hseed := fw_first_band_seed_radius_le_three_halves lower hnlo (by omega)
  have hgrowth := fw_growth_first_band_midpoint_gate n hnlo hnhi X hX
  dsimp only [fwFrozenCYLineRadius]
  change (9/2 : ℝ) + X * (23/924 : ℝ) * Real.sqrt (94 * Real.log (8*(n : ℝ)+8)) +
      X * (2/235 : ℝ) * Real.sqrt ((54*((n/450 : ℕ) : ℝ)+4)*Real.log (8*(n : ℝ)+8)) +
      Real.sqrt (((11/2 : ℝ)*((2^30 : ℕ) : ℝ)^2)*Real.log (4 * (((n+n)+2 : ℕ) : ℝ))/2) +
      ((Nat.clog 2 (6*n) : ℝ)*(8*(X/6)) + 3*(X/6)/(n : ℝ) + 2*(X/6)) +
      (257/250 : ℝ)*X + (19033/450 : ℝ)*(201/10000 : ℝ)*X +
      ((1+2*(9*0+6 : ℕ)*(4262317/50000000 : ℝ))*X + 3*X) ≤ 34*X
  change _ ≤ (3/2 : ℝ) * X at hseed
  nlinarith [hB', hW', hseed, hgrowth, hconst]

/-- A supplied target spread of at most `10X` strictly meets FW18's routing
budget. This does not construct prime targets or prove their spread. -/
theorem fw_first_band_cy_routing_budget_of_spread
    (lower : RSIndexLower) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (D : ℝ) (hD : D ≤ 10 * (poolMaximum n : ℝ)) :
    fwFrozenCYLineRadius n + D <
      (518481/500000 : ℝ) * (((n/450)*poolMaximum n : ℕ) : ℝ) := by
  have hXpos : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hX : (0 : ℝ) ≤ poolMaximum n := hXpos.le
  have hq : 43 ≤ n/450 := by omega
  have hqR : (43 : ℝ) ≤ ((n/450 : ℕ) : ℝ) := by exact_mod_cast hq
  have hmul := mul_nonneg (show 0 ≤ ((n/450 : ℕ) : ℝ) - 43 by linarith) hX
  have hline := fw_frozen_cy_line_radius_le_34 lower hnlo hnhi
  push_cast
  nlinarith

/-- Across `19485 ≤ n ≤ 35733`, the frozen CY line radius is bounded by `36 * poolMaximum n`. -/
theorem fw_frozen_cy_line_radius_le_36
    (lower : RSIndexLower) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    fwFrozenCYLineRadius n ≤ (36 : ℝ) * poolMaximum n := by
  let X : ℝ := poolMaximum n
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hXlarge : 4 * (2^30 : ℝ) < X := by
    dsimp [X]
    exact_mod_cast fw_poolMaximum_gt_four_seed lower hnlo
  have hconst : (9/2 : ℝ) ≤ X/100 := by norm_num at hXlarge ⊢; linarith
  have hB := fw_first_band_bridge_sqrt_le_35 hnhi
  have hW := fw_wide_sqrt_le_236 hnhi
  have hB' := mul_le_mul_of_nonneg_left hB (show 0 ≤ X * (23/924 : ℝ) by positivity)
  have hW' := mul_le_mul_of_nonneg_left hW (show 0 ≤ X * (2/235 : ℝ) by positivity)
  have hseed := fw_first_band_seed_radius_le_three_halves lower hnlo hnhi
  have hu : Nat.clog 2 (6 * n) ≤ 18 := by
    apply Nat.clog_le_of_le_pow
    norm_num
    omega
  have huR : (Nat.clog 2 (6 * n) : ℝ) ≤ 18 := by exact_mod_cast hu
  have hnR : (19485 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlo
  have hdiv : 3 * (X / 6) / (n : ℝ) ≤ X / 38970 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hgrowth : (Nat.clog 2 (6 * n) : ℝ) * (8 * (X / 6)) + 3 * (X / 6) / (n : ℝ) + 2 * (X / 6) ≤
      (24 + 1 / 3 + 1 / 38970 : ℝ) * X := by
    nlinarith
  dsimp only [fwFrozenCYLineRadius]
  change (9/2 : ℝ) + X * (23/924 : ℝ) * Real.sqrt (94 * Real.log (8*(n : ℝ)+8)) +
      X * (2/235 : ℝ) * Real.sqrt ((54*((n/450 : ℕ) : ℝ)+4)*Real.log (8*(n : ℝ)+8)) +
      Real.sqrt (((11/2 : ℝ)*((2^30 : ℕ) : ℝ)^2)*Real.log (4 * (((n+n)+2 : ℕ) : ℝ))/2) +
      ((Nat.clog 2 (6*n) : ℝ)*(8*(X/6)) + 3*(X/6)/(n : ℝ) + 2*(X/6)) +
      (257/250 : ℝ)*X + (19033/450 : ℝ)*(201/10000 : ℝ)*X +
      ((1+2*(9*0+6 : ℕ)*(4262317/50000000 : ℝ))*X + 3*X) ≤ 36*X
  change _ ≤ (3/2 : ℝ) * X at hseed
  nlinarith [hB', hW', hseed, hgrowth, hconst]

end
end Sude
