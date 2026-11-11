import Sude.FWSeedTraceBridgeGrid

/-! Abstract trace growth with explicit prior bridge and seed protection. -/
namespace Sude
noncomputable section

local instance : DecidableEq BTSelectedStage := Classical.decEq _

/-- Under the published BMOR and RS hypotheses, one set of five nominal FW
bridge batches works for each supplied screened-pool trace whose reserved
set contains the actual selected bridge values and a supplied retained set.
Every growth-stage footprint then avoids that whole union, and a qualifying
abstract seed/trace grid extends through X. The retained set's identity and
seed properties, trace existence and coverage, physical placement, and line
geometry remain explicit or unproved. -/
theorem bmor_fw_protected_bridges_extend_every_screened_trace
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    ∃ batches : ℕ → List DoublePair,
      (∀ j < 5, FWBridgeSequentialValid n ∅ batches j) ∧
      (∀ i < 5, ∀ j < 5, i ≠ j →
        Disjoint (doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))
          (doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j))) ∧
      (∀ j ≤ 5, (priorBridgeReservation ∅ (Finset.range j) batches).card ≤
        (∅ : Finset ℕ).card + j * (4 * (3 * (n + 8)))) ∧
      (∀ (retained reserved final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage)
        (index : Fin (3 * (n + 8))),
        priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained ⊆ reserved →
        BTGrowingTrace 2 (6 * (n + 8))
          ((poolFinset n).filter (fun p => 43 < p) \ reserved) 32 final last stages →
        (poolMaximum n : ℝ) / 23 ≤ last →
        (∀ stage ∈ stages,
          Disjoint stage.footprint (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained)) ∧
        CompleteEvenGrid
          ((fwSeedTraceLabels stages).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
            (Finset.range 5).image (Sum.inr : ℕ → Sum (Sum (Fin 16) BTSelectedStage) ℕ))
          (joinedBridgeGap fwSeedTraceGap batches index)
          (last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j) ∧
        (poolMaximum n : ℝ) ≤
          ((last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j : ℕ) : ℝ)) := by
  obtain ⟨batches, hvalid, hdisjoint, hcard, hgrow⟩ :=
    bmor_fw_bridges_extend_every_screened_trace bmor upper lower hnlo hnhi
  refine ⟨batches, hvalid, hdisjoint, hcard, ?_⟩
  intro retained reserved final last stages index hprotect htrace hcoverage
  have havoids : ∀ stage ∈ stages,
      Disjoint stage.footprint (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained) := by
    intro stage hs
    apply Finset.disjoint_left.mpr
    intro p hp hprotected
    have hunused := htrace.footprints_subset stage hs hp
    exact (Finset.mem_sdiff.mp hunused).2 (hprotect hprotected)
  exact ⟨havoids, hgrow reserved final last stages index htrace hcoverage⟩

end
end Sude
