import Sude.FWSecondAffinePhase

/-! The first-band absolute stock envelope and its deletion reserve. -/

namespace Sude
noncomputable section

/-- Absolute conservative mass at global stage j. -/
def fwVaryingStockMass (X : ℝ) (j : ℕ) : ℝ :=
  ((403 / 10000 : ℝ) - 2 * (1 / 69780 : ℝ) * j) * X

/-- The future envelope plus the actual removal reserve is bounded by the
current envelope. `Q` is the absolute number of selected pairs. -/
theorem fw_varying_mass_future_reserve {X Q : ℝ} {j fuel : ℕ}
    (hQ : Q ≤ (1 / 69780 : ℝ) * X) :
    fwVaryingStockMass X (j + fuel) + 2 * Q * fuel ≤ fwVaryingStockMass X j := by
  unfold fwVaryingStockMass
  push_cast
  have h := mul_le_mul_of_nonneg_right hQ (show (0 : ℝ) ≤ 2 * fuel by positivity)
  nlinarith

/-- Any fixed terminal floor bounded by the future envelope can reserve
all subsequent absolute removals. -/
theorem fw_varying_mass_terminal_reserve {X Q Mf stock : ℝ} {j fuel : ℕ}
    (hQ : Q ≤ (1 / 69780 : ℝ) * X)
    (hMf : Mf ≤ fwVaryingStockMass X (j + fuel))
    (hstock : fwVaryingStockMass X j ≤ stock) :
    Mf + 2 * Q * fuel ≤ stock := by
  have h := fw_varying_mass_future_reserve (j := j) (fuel := fuel) hQ
  linarith

/-- The fixed absolute terminal mass is below every envelope up to stage 238. -/
theorem fw_varying_mass_floor_238 {X : ℝ} {j : ℕ} (hX : 0 ≤ X) (hj : j ≤ 238) :
    (3257 / 100000 : ℝ) * X ≤ fwVaryingStockMass X j := by
  unfold fwVaryingStockMass
  have hjR : (j : ℝ) ≤ 238 := by exact_mod_cast hj
  have hcoef : (3257 / 100000 : ℝ) ≤ 403 / 10000 - 2 * (1 / 69780 : ℝ) * j := by linarith
  exact mul_le_mul_of_nonneg_right hcoef hX

/-- The fixed conservative terminal mass plus actual fuel deletion is
covered by the current variable envelope through the 238-stage horizon. -/
theorem fw_varying_fixed_terminal_reserve {X Q stock : ℝ} {j fuel : ℕ}
    (hX : 0 ≤ X) (hQ : Q ≤ (1 / 69780 : ℝ) * X)
    (hsteps : j + fuel ≤ 238) (hstock : fwVaryingStockMass X j ≤ stock) :
    (3257 / 100000 : ℝ) * X + 2 * Q * fuel ≤ stock := by
  exact fw_varying_mass_terminal_reserve hQ
    (fw_varying_mass_floor_238 hX hsteps) hstock

/-- A single physical removal is reserved by the next envelope, not the
current envelope plus an additional pair charge. -/
theorem fw_varying_mass_one_step {X Q stock : ℝ} {j : ℕ}
    (hQ : Q ≤ (1 / 69780 : ℝ) * X)
    (hstock : fwVaryingStockMass X j ≤ stock) :
    fwVaryingStockMass X (j + 1) + 2 * Q ≤ stock := by
  have h := fw_varying_mass_future_reserve (j := j) (fuel := 1) hQ
  norm_num at h
  linarith

/-- The first-band charge and current-stage absolute mass bound follow from
the same supplied trace and witnesses. -/
theorem fw_first_band_varying_stock_mass
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
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
  have henv := fw_first_band_ww4_envelopes_from_imports bmor lower upper upperSharp hnlo hnhi
    hsteps hVlo hVhi
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
