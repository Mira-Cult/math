import Sude.FWSeedTraceGrid
import Sude.FWBridgeFiveGrid

/-! Compose supplied screened traces with the selected nominal FW bridges. -/
namespace Sude
noncomputable section

local instance : DecidableEq BTSelectedStage := Classical.decEq _

/-- One selected family of five nominal bridge batches extends every
supplied screened-pool trace beginning at the abstract sixteen-seed radius
32 and reaching `X/23`, for every chosen block index, to a complete
abstract even grid through `X`. The trace, its reserved set and its final
coverage are explicit inputs. This does not construct the source's mixed
recipe, physical seed pairs, bridge slots, or line geometry. -/
theorem bmor_fw_bridges_extend_every_screened_trace
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    ∃ batches : ℕ → List DoublePair,
      (∀ j < 5, FWBridgeSequentialValid n ∅ batches j) ∧
      (∀ i < 5, ∀ j < 5, i ≠ j →
        Disjoint (doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))
          (doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j))) ∧
      (∀ j ≤ 5, (priorBridgeReservation ∅ (Finset.range j) batches).card ≤
        (∅ : Finset ℕ).card + j * (4 * (3 * (n + 8)))) ∧
      (∀ (reserved final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage)
        (index : Fin (3 * (n + 8))),
        BTGrowingTrace 2 (6 * (n + 8))
          ((poolFinset n).filter (fun p => 43 < p) \ reserved) 32 final last stages →
        (poolMaximum n : ℝ) / 23 ≤ last →
        CompleteEvenGrid
          ((fwSeedTraceLabels stages).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
            (Finset.range 5).image (Sum.inr : ℕ → Sum (Sum (Fin 16) BTSelectedStage) ℕ))
          (joinedBridgeGap fwSeedTraceGap batches index)
          (last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j) ∧
        (poolMaximum n : ℝ) ≤
          ((last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j : ℕ) : ℝ)) := by
  obtain ⟨batches, hvalid, hdisjoint, hcard, hgrow⟩ :=
    bmor_fw_five_bridge_batches_grow_every_grid bmor upper lower hnlo hnhi
  refine ⟨batches, hvalid, hdisjoint, hcard, ?_⟩
  intro reserved final last stages index htrace hcoverage
  obtain ⟨hgrid, heven, _⟩ :=
    fw_screened_seed_trace_bridge_grid n reserved final last stages htrace hcoverage
  exact hgrow (Sum (Fin 16) BTSelectedStage) index (fwSeedTraceLabels stages)
    fwSeedTraceGap last hgrid heven hcoverage

end
end Sude
