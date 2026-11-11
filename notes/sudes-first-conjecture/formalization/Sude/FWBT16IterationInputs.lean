import Sude.FWBT16IterationFromCharge
import Sude.FWThetaInputs

/-! Thin source-input adapters for the shared stage-charge BT16 iterator.
No new trace or analytic input is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- Iterate actual selected BT16 stages without charging the 6Q candidate
matching: each appended stage retains Q pairs and deletes exactly 2Q values.
The width record uses global stage indices and actual accumulated radii. -/
theorem fw_bt16_chosen_iterate_first_band_of_theta
    (mv : MVBrunTitchmarsh)
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (fuel : ℕ) (stock : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 stock last stages)
    (hbudget : stages.length + fuel ≤ 238) (hradius : 171331843 ≤ last) :
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    let width : ℕ → ℕ → ℝ := fun j R =>
      8 * ((3981035 / 10000000 : ℝ) * fwFirstBandMu j * R - 1 / 2)
    ∃ (final : Finset ℕ) (last' : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last' (stages ++ extra) ∧
      BTGrowingTrace 2 (6 * (n + 8)) stock last final last' extra ∧
      extra.length ≤ fuel ∧ stages.length + extra.length ≤ 238 ∧
      ((poolMaximum n : ℝ) / 23 ≤ last' ∨ extra.length = fuel) ∧
      BTWidthTrace width stages.length last extra ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      final ⊆ stock ∧ final.card + 2 * (6 * (n + 8)) * extra.length = stock.card ∧
      (stages ++ extra).Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) := by
  have hlog := fw_poolMaximum_log_gt_181_eighths lower hnlo
  have hratio := fw_actual_index_ratio_of_theta bmor lower upper hnlo (by omega)
  have hQ := fw_first_band_stage_charge_from_fw3 hnlo hlog hratio
  exact fw_bt16_chosen_iterate_first_band_of_charge mv upperSharp hnlo hnhi hQ
    batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks
    fuel stock last stages trace hbudget hradius

/-- Iterate actual selected BT16 stages without charging the 6Q candidate
matching: each appended stage retains Q pairs and deletes exactly 2Q values.
The width record uses global stage indices and actual accumulated radii. -/
theorem fw_bt16_chosen_iterate_first_band_via_charge
    (mv : MVBrunTitchmarsh)
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (fuel : ℕ) (stock : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 stock last stages)
    (hbudget : stages.length + fuel ≤ 238) (hradius : 171331843 ≤ last) :
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    let width : ℕ → ℕ → ℝ := fun j R =>
      8 * ((3981035 / 10000000 : ℝ) * fwFirstBandMu j * R - 1 / 2)
    ∃ (final : Finset ℕ) (last' : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last' (stages ++ extra) ∧
      BTGrowingTrace 2 (6 * (n + 8)) stock last final last' extra ∧
      extra.length ≤ fuel ∧ stages.length + extra.length ≤ 238 ∧
      ((poolMaximum n : ℝ) / 23 ≤ last' ∨ extra.length = fuel) ∧
      BTWidthTrace width stages.length last extra ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      final ⊆ stock ∧ final.card + 2 * (6 * (n + 8)) * extra.length = stock.card ∧
      (stages ++ extra).Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) := by
  have hlog := fw_poolMaximum_log_gt_181_eighths lower hnlo
  have hratio := fw_actual_index_ratio bmor lower upper hnlo (by omega)
  have hQ := fw_first_band_stage_charge_from_fw3 hnlo hlog hratio
  exact fw_bt16_chosen_iterate_first_band_of_charge mv upperSharp hnlo hnhi hQ
    batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks
    fuel stock last stages trace hbudget hradius

end
end Sude
