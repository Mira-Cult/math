import Sude.FWWheelPairSupply
import Sude.FWEarlyReservationCard
import Sude.ScreenedPool
import Sude.FWSharpIndex

/-! Actual FW screened stock after the source early reservations and an
explicit supplied growth trace. This is accounting, not a trace construction
or a proof of the source's numerical WW4 inequalities. -/
namespace Sude
noncomputable section

/-- The bridge reservation, retained seed values and a supplied wide footprint
fit the FW10 early budget. Wide-block existence and placement are not assumed
or inferred; only its actual set-cardinality bound is used. -/
theorem fw_wheel_early_reserved_card (n : ℕ) (batches : ℕ → List DoublePair)
    (hlen : ∀ j < 5, (batches j).length = 3 * (n + 8))
    (retained wide : Finset ℕ)
    (hretained : retained.card = 2 * (6 * (n + 8)) * 16)
    (hwide : wide.card ≤ 4 * (3 * (n / 450) * (3 * (n + 8)))) :
    ((priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained) ∪ wide).card ≤
      fwEarlyBudget n := by
  let early := priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained
  have hearly := fw_early_reservation_card_budget n batches hlen retained early hretained (by
    dsimp [early]
    exact Finset.Subset.rfl)
  have hunion := Finset.card_union_le early wide
  dsimp [early] at *
  omega

/-- A supplied source-counted wide block list has at most the expected four
reserved endpoints per block, without a disjointness hypothesis. -/
theorem fw_wheel_wide_batch_card (n : ℕ) (blocks : List DoublePair)
    (hlen : blocks.length = 3 * (n / 450) * (3 * (n + 8))) :
    (doubleBatchLow blocks ∪ doubleBatchHigh blocks).card ≤
      4 * (3 * (n / 450) * (3 * (n + 8))) := by
  have hl := doubleBatchLow_card_le blocks
  have hh := doubleBatchHigh_card_le blocks
  have hu := Finset.card_union_le (doubleBatchLow blocks) (doubleBatchHigh blocks)
  rw [hlen] at hl hh
  omega

/-- A uniform rational upper bound for the actual per-stage charge `Q/X`,
conditional on the explicitly supplied sharp Rosser--Schoenfeld estimate.
It is a coarse bound, not the source's tighter band-wise envelope. -/
theorem fw_wheel_actual_stage_charge_bound (sharp : RSIndexLowerSharp) {n : ℕ}
    (hn : 19485 ≤ n) :
    ((6 * (n + 8) : ℕ) : ℝ) ≤ (1 / 68000 : ℝ) * poolMaximum n := by
  have hnR : (19485 : ℝ) ≤ n := by exact_mod_cast hn
  have hx := fw_poolMaximum_gt_twenty_one_sq sharp hn
  push_cast
  nlinarith

/-- A bounded first-band WW4 quota check with the frozen FW coefficients.
The sharper index ratio and the upper envelope V are explicit hypotheses;
the theorem does not establish either source-band bound. -/
theorem fw_wheel_ww4_first_band_quota {n : ℕ} {X V : ℝ}
    (hn : 19483 ≤ n) (hX : (43 / 2 : ℝ) * (n : ℝ)^2 ≤ X)
    (hVpos : 0 < V) (hV : V ≤ 231 / 10) :
    2 * (23 / 48 - 3981035 / 10000000 : ℝ) *
      (((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V)^2 ≥
    2 * 6 * (((6 * (n + 8) : ℕ) : ℝ) / X) := by
  have hnR : (19483 : ℝ) ≤ n := by exact_mod_cast hn
  have hXpos : 0 < X := by nlinarith
  have hbound : (69780 : ℝ) * (6 * ((n : ℝ) + 8)) ≤ (43 / 2 : ℝ) * (n : ℝ)^2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 19483)]
  have hq : (((6 * (n + 8) : ℕ) : ℝ) / X) ≤ (1 / 69780 : ℝ) := by
    apply (div_le_iff₀ hXpos).2
    push_cast
    nlinarith
  have hmf : (3257 / 100000 : ℝ) ≤
      ((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V := by
    apply (le_div_iff₀ hVpos).2
    nlinarith
  have hmf2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ 3257 / 100000 by norm_num) hmf 2
  have heps : (0 : ℝ) ≤ 23 / 48 - 3981035 / 10000000 := by norm_num
  have hprod := mul_le_mul_of_nonneg_left hmf2 heps
  have hrat : (23 / 48 - 3981035 / 10000000 : ℝ) * (3257 / 100000 : ℝ)^2 ≥
      6 / 69780 := by norm_num
  nlinarith

/-- Every supplied actual trace pays its initial bridge, retained and wide
reservations and exactly `2Q` entries per stage. The estimate retains the
actual stage count, with no stage cap or numerical lower bound assumed. -/
theorem fw_wheel_screened_actual_stock
    (n : ℕ) (hn : 13 ≤ n * n) (batches : ℕ → List DoublePair)
    (hlen : ∀ j < 5, (batches j).length = 3 * (n + 8))
    (retained wide : Finset ℕ)
    (hretained : retained.card = 2 * (6 * (n + 8)) * 16)
    (hwide : wide.card ≤ 4 * (3 * (n / 450) * (3 * (n + 8))))
    (radius last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        ((priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained) ∪ wide))
      radius final last stages) :
    n * n ≤ final.card + fwEarlyBudget n + 13 +
      2 * (6 * (n + 8)) * stages.length := by
  let reserved := (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained) ∪ wide
  have hres := fw_wheel_early_reserved_card n batches hlen retained wide hretained hwide
  have hscreen := (screened_pool_after_reservations n reserved hn).1
  have htrace := trace.final_accounting
  dsimp [reserved] at hscreen
  omega

/-- A supplied source-band lower baseline and upper per-stage charge become
an actual normalized stock bound for the trace's final screened set. These
are input inequalities, not numerically certified FW13 gates. -/
theorem fw_wheel_screened_normalized_stock
    (n : ℕ) (hn : 13 ≤ n * n) (batches : ℕ → List DoublePair)
    (hlen : ∀ j < 5, (batches j).length = 3 * (n + 8))
    (retained wide : Finset ℕ)
    (hretained : retained.card = 2 * (6 * (n + 8)) * 16)
    (hwide : wide.card ≤ 4 * (3 * (n / 450) * (3 * (n + 8))))
    (radius last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        ((priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained) ∪ wide))
      radius final last stages)
    (m₀ qbar : ℝ)
    (hbaseline : m₀ * (poolMaximum n : ℝ) ≤
      ((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n)
    (hQ : ((6 * (n + 8) : ℕ) : ℝ) ≤ qbar * (poolMaximum n : ℝ)) :
    (m₀ - 2 * qbar * stages.length) * (poolMaximum n : ℝ) ≤ final.card := by
  have hstock := fw_wheel_screened_actual_stock n hn batches hlen retained wide
    hretained hwide radius last final stages trace
  have hstockR : ((n * n : ℕ) : ℝ) ≤ (final.card : ℝ) + fwEarlyBudget n + 13 +
      2 * ((6 * (n + 8) : ℕ) : ℝ) * stages.length := by exact_mod_cast hstock
  have hsteps : (0 : ℝ) ≤ 2 * (stages.length : ℝ) := by positivity
  have hq := mul_le_mul_of_nonneg_left hQ hsteps
  nlinarith

end
end Sude
