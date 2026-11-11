import Sude.FWEnhancedBT16Entry
import Sude.FWBT16ChosenIteration

/-! Carry the enhanced first-band witness through at most ten actual BT16
stages, stopping at actual crossing. No crossing is inferred from fuel alone. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- For the same selected early witnesses, retain the enhanced trace and,
if it completes 228 stages, append up to ten actual-radius BT16 stages.
The global-index width record, suffix trace, and exact Q-pair accounting all
refer to that same completed trace and its remaining stock. -/
theorem fw_enhanced_from_seed_stop_or_ten_bt16
    (mv : MVBrunTitchmarsh)
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8))) :
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    let width : ℕ → ℕ → ℝ := fun j R =>
      8 * ((3981035 / 10000000 : ℝ) * fwFirstBandMu j * R - 1 / 2)
    ∃ (stock : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 stock last stages ∧
      stages.length ≤ 228 ∧
      stock ⊆ initial ∧
      stock.card + 2 * (6 * (n + 8)) * stages.length = initial.card ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) stages ∧
      (∀ stage ∈ stages, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      ((poolMaximum n : ℝ) / 23 ≤ last ∨
        (FWEnhancedFromSeedComplete n last stages ∧ stages.length = 228 ∧
          174846346 ≤ last ∧
          fwFirstBandMu stages.length * (poolMaximum n : ℝ) ≤ (stock.card : ℝ) ∧
          ∃ (final : Finset ℕ) (last' : ℕ) (extra : List BTSelectedStage),
            BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last' (stages ++ extra) ∧
            BTGrowingTrace 2 (6 * (n + 8)) stock last final last' extra ∧
            extra.length ≤ 10 ∧ stages.length + extra.length ≤ 238 ∧
            ((poolMaximum n : ℝ) / 23 ≤ last' ∨ extra.length = 10) ∧
            BTWidthTrace width stages.length last extra ∧
            NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
            final ⊆ stock ∧ final.card + 2 * (6 * (n + 8)) * extra.length = stock.card ∧
            (stages ++ extra).Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
            (∀ stage ∈ extra, Disjoint stage.footprint
              (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)))) := by
  dsimp only
  obtain ⟨stock, last, stages, trace, hcap, hstocksub, hstockcard, hnarrow, havoid, hstop⟩ :=
    fw_enhanced_from_seed_stop_or_bt16_numeric_entry bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks
  refine ⟨stock, last, stages, trace, hcap, hstocksub, hstockcard, hnarrow, havoid, ?_⟩
  rcases hstop with hcross | ⟨hcomplete, hlen, hlast, hstock, hnorm, hwidth⟩
  · exact Or.inl hcross
  · right
    refine ⟨hcomplete, hlen, hlast, hstock, ?_⟩
    exact fw_bt16_chosen_iterate_first_band mv bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 10 stock last stages trace
      (by omega) (by omega)

end
end Sude
