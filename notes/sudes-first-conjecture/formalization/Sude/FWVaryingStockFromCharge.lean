import Sude.FWVaryingStockMass

/-! The first-band varying-stock accounting from an explicitly supplied
charge bound. No prime-count, theta, trace-existence, or placement assertion
is made here. -/
namespace Sude
noncomputable section

/-- The same supplied trace and witnesses have the first-band varying stock
lower bound when the actual per-stage charge obeys the supplied envelope. -/
theorem fw_first_band_varying_stock_mass_of_charge
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (hQ : ((6 * (n + 8) : ℕ) : ℝ) ≤ (1 / 69780 : ℝ) * (poolMaximum n : ℝ))
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
      radius final last stages) :
    fwVaryingStockMass (poolMaximum n) stages.length ≤ (final.card : ℝ) := by
  have hn : 13 ≤ n * n := by nlinarith
  have hbase := fw_first_band_stock_baseline upperSharp hnlo hnhi
  have hstock := (fw_wheel_witness_trace_stock hn batches hvalid candidates hcard kept hsub hkept
    hinj blocks hblocks radius last final stages trace).2.2.2.1
  have hstockR : ((n * n : ℕ) : ℝ) ≤ (final.card : ℝ) + fwEarlyBudget n + 13 +
      2 * ((6 * (n + 8) : ℕ) : ℝ) * stages.length := by exact_mod_cast hstock
  have hqSteps := mul_le_mul_of_nonneg_left hQ (show (0 : ℝ) ≤ 2 * (stages.length : ℝ) by positivity)
  unfold fwVaryingStockMass
  push_cast at *
  nlinarith

end
end Sude
