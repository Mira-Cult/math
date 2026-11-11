import Sude.FWVaryingStockMass
import Sude.FWMixedAffineSlope
import Sude.FWMixedAffineVaryingIteration

/-! First-band varying-mass continuation with an explicit wheel-origin gate. -/

namespace Sude
noncomputable section

/-- The same mass never exceeds its initial coefficient, uniformly in j. -/
theorem fw_varying_mass_initial_cap {X : ℝ} (hX : 0 < X) (j : ℕ) :
    ((403 / 10000 : ℝ) - 2 * (1 / 69780 : ℝ) * j) * X ≤
      (403 / 10000 : ℝ) * X := by
  apply mul_le_mul_of_nonneg_right _ hX.le
  have hj : (0 : ℝ) ≤ j := by positivity
  linarith

/-- The affine slope gate holds for every indexed wheel at every stage. -/
theorem fw_varying_mass_slope (i : Fin 8) {X : ℝ} (hX : 0 < X) (j : ℕ) :
    fwAffineSlope (3981035 / 10000000) 2
      (((403 / 10000 : ℝ) - 2 * (1 / 69780 : ℝ) * j) * X)
      1 X / fwMixedWheelRho i ≤ 1 := by
  have hrho := fw_mixed_affine_density_gt_quarter i
  have hrhopos : 0 < fwMixedWheelRho i := by linarith
  have hm := fw_varying_mass_initial_cap hX j
  apply (div_le_one hrhopos).2
  unfold fwAffineSlope
  norm_num only [one_mul]
  apply (div_le_iff₀ hX).2
  have hprod := mul_le_mul_of_nonneg_right hrho.le hX.le
  nlinarith

/-- The fixed absolute terminal mass satisfies the affine quota. -/
theorem fw_varying_mass_fixed_quota
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) :
    ((6 * (6 * (n + 8)) : ℕ) : ℝ) * poolMaximum n ≤
      (1 / (2 * (1 + 1 / (23 : ℝ))) - 3981035 / 10000000) *
        ((3257 / 100000 : ℝ) * poolMaximum n)^2 := by
  convert fw_first_affine_absolute_quota bmor lower upper upperSharp hnlo hnhi using 1; norm_num

/-- First-band source specialization of the varying-mass wheel continuation.
The radius must satisfy the origin gate for the selected wheel. -/
theorem fw_first_band_varying_affine_iterate (i : Fin 8)
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (fuel : ℕ) (last : ℕ) (S : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 S last stages)
    (hcap : stages.length + fuel ≤ 238)
    (hlast : 0 < last) (heven : 2 ∣ last)
    (hshift : 0 < (last : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n)) :
    ∃ (final : Finset ℕ) (actualFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8))
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final actualFinal (stages ++ extra) ∧
      extra.length ≤ fuel ∧ final ⊆ S ∧
      final.card + 2 * (6 * (n + 8)) * extra.length = S.card ∧
      fwVaryingStockMass (poolMaximum n) (stages ++ extra).length ≤ (final.card : ℝ) ∧
      ((poolMaximum n : ℝ) / 23 ≤ actualFinal ∨ extra.length = fuel) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      last ≤ actualFinal ∧ 2 ∣ actualFinal ∧
      FWMixedAffineVaryingSchedule i n 23 ((3257 / 100000 : ℝ) * poolMaximum n)
        (3981035 / 10000000) (fwVaryingStockMass (poolMaximum n))
        stages.length last actualFinal extra := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hMf : (0 : ℝ) < (3257 / 100000 : ℝ) * poolMaximum n := by positivity
  have hscreen : S ⊆ (poolFinset n).filter (fun p => 43 < p) :=
    trace.final_accounting.1.trans Finset.sdiff_subset
  obtain ⟨hq, hstock⟩ := fw_first_band_varying_stock_mass bmor lower upper upperSharp hnlo hnhi
    batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last S stages trace (by omega)
  have hmass : ∀ k < 238, (3257 / 100000 : ℝ) * poolMaximum n ≤ fwVaryingStockMass (poolMaximum n) k := by
    intro k hk
    exact fw_varying_mass_floor_238 hX.le (by omega)
  have hslope : ∀ k < 238, fwAffineSlope (3981035 / 10000000) 2
      (fwVaryingStockMass (poolMaximum n) k) 1 (poolMaximum n) / fwMixedWheelRho i ≤ 1 := by
    intro k hk
    exact fw_varying_mass_slope i hX k
  have hdrop : ∀ k < 238, fwVaryingStockMass (poolMaximum n) (k + 1) +
      ((2 * (6 * (n + 8)) : ℕ) : ℝ) ≤ fwVaryingStockMass (poolMaximum n) k := by
    intro k hk
    have hh := fw_varying_mass_one_step (j := k) hq (le_refl (fwVaryingStockMass (poolMaximum n) k))
    push_cast at *
    linarith
  exact fw_mixed_affine_varying_global_iterate i (cap := 238) fuel trace 23
    ((3257 / 100000 : ℝ) * poolMaximum n) (3981035 / 10000000)
    (fwVaryingStockMass (poolMaximum n)) hlast heven (by norm_num) hscreen
    (by norm_num) hMf (by norm_num) hshift
    (fw_varying_mass_fixed_quota bmor lower upper upperSharp hnlo hnhi)
    hcap hmass hslope hdrop hstock

end
end Sude
