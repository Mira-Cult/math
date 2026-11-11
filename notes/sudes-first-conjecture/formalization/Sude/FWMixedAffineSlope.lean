import Sude.FWMixedAffineStage
import Sude.FWSharpIndex

/-! The slope gate for each frozen FW affine wheel, using actual screened
pool stock and the existing sharp prime-index estimate. No affine origin,
stock lower bound, mixed trace or crossing is asserted. -/
namespace Sude
noncomputable section

/-- Every one of the eight explicitly frozen affine densities exceeds 1/4. -/
theorem fw_mixed_affine_density_gt_quarter (i : Fin 8) :
    (1 / 4 : ℝ) < fwMixedWheelRho i := by
  fin_cases i <;> norm_num [fwMixedWheelRho]

/-- In FW's order range the frozen first-band eta makes the affine slope
strictly less than one for all eight wheels and any mass bounded by the
actual remaining pool size. The upper bound uses only the full pool count,
so it applies to any screened subset and any supplied growth stage. -/
theorem fw_mixed_affine_slope_from_pool_stock (sharp : RSIndexLowerSharp)
    {n : ℕ} (hn : 19485 ≤ n) (i : Fin 8) (S : Finset ℕ)
    (hS : S ⊆ poolFinset n) (M : ℝ) (hM : M ≤ S.card) :
    fwAffineSlope (3981035 / 10000000) 2 M 1 (poolMaximum n) /
      fwMixedWheelRho i < 1 := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hrho := fw_mixed_affine_density_gt_quarter i
  have hrhopos : 0 < fwMixedWheelRho i := by linarith
  have hcard : S.card ≤ n*n := by
    have h := Finset.card_le_card hS
    simpa [poolFinset_card] using h
  have hN : (S.card : ℝ) ≤ (n : ℝ)^2 := by
    have h : (S.card : ℝ) ≤ (n : ℝ) * n := by exact_mod_cast hcard
    nlinarith
  have hMX : M ≤ (n : ℝ)^2 := hM.trans hN
  have hx := fw_poolMaximum_gt_twenty_one_sq sharp hn
  have hρX := mul_lt_mul_of_pos_right hrho hX
  have hNnonneg : 0 ≤ (n : ℝ)^2 := sq_nonneg _
  apply (div_lt_one hrhopos).2
  unfold fwAffineSlope
  norm_num only [one_mul]
  apply (div_lt_iff₀ hX).2
  nlinarith

end
end Sude
