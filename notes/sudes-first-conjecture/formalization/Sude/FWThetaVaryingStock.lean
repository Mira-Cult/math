import Sude.FWVaryingStockMass
import Sude.FWThetaInputs

/-! First-band varying stock bound from explicit finite theta and RS inputs,
    for a supplied screened trace. No trace or witness existence is asserted. -/
namespace Sude
noncomputable section

/-- The first-band charge and current-stage absolute mass bound follow from
the same supplied trace and witnesses. -/
theorem fw_first_band_varying_stock_mass_of_theta
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (radius last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      radius final last stages)
    (hsteps : stages.length ≤ 238) :
    let X : ℝ := poolMaximum n
    let Q : ℝ := (6 * (n + 8) : ℕ)
    Q ≤ (1 / 69780 : ℝ) * X ∧
      fwVaryingStockMass X stages.length ≤ (final.card : ℝ) := by
  dsimp only
  have hn : 13 ≤ n * n := by nlinarith
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hbase := fw_first_band_stock_baseline upperSharp hnlo hnhi
  obtain ⟨hVlo, hVhi⟩ := fw_first_band_pointwise_log_bounds upperSharp lower hnlo hnhi
  have henv := fw_first_band_ww4_envelopes_of_aggregate lower upper upperSharp hnlo hnhi
    hsteps (fw_pool_odd_count_uniform_of_theta bmor lower upper hnlo (by omega)) hVlo hVhi
  dsimp only at henv
  have hq := henv.2.1
  have hstock := (fw_wheel_witness_trace_stock hn batches hvalid candidates hcard kept hsub hkept
    hinj blocks hblocks radius last final stages trace).2.2.2.1
  have hstockR : ((n * n : ℕ) : ℝ) ≤ (final.card : ℝ) + fwEarlyBudget n + 13 +
      2 * ((6 * (n + 8) : ℕ) : ℝ) * stages.length := by exact_mod_cast hstock
  have hqSteps := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 2 * (stages.length : ℝ) by positivity)
  constructor
  · exact hq
  · unfold fwVaryingStockMass
    push_cast at *
    nlinarith

end
end Sude
