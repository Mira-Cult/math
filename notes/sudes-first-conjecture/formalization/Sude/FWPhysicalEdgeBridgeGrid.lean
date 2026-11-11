import Sude.FWPhysicalEdgeWitnessGrid
import Sude.FWPhysicalBridgeWideTrace

/-! Compose the installed per-edge seed and growth grid with the same
physical bridge batches. Crossing and installation remain explicit hypotheses;
no simultaneous switchability or line-sum result is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Under actual crossing, each physical edge grid extends through `X` using
the same bridge batches. Early-role preservation preserves seed cells, and
the seed, growth and bridge layers use the supplied permutation triple. -/
theorem fw_physical_edge_bridge_witness_grid {n L : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n)) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hav : ∀ x, sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard x ∈
      poolFinset n \ priorBridgeReservation ∅ (Finset.range 5) batches)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (hrmap : rows.map Prod.fst = bridgeRepeatedPermutations 5 p)
    (hcmap : cols.map Prod.fst = bridgeRepeatedPermutations 5 p)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hsrmap : sr.map Prod.fst = bridgeRepeatedPermutations 16 p)
    (hscmap : sc.map Prod.fst = bridgeRepeatedPermutations 16 p)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hso : ∀ x, entry old (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x)))
    (hplace : ∀ x, entry old (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    {initial final : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last stages)
    (hcross : (poolMaximum n : ℝ) / 23 ≤ last)
    (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3)
    (hgc : gc.length = stages.length * 3)
    (hgrmap : gr.map Prod.fst = bridgeRepeatedPermutations stages.length p)
    (hgcmap : gc.map Prod.fst = bridgeRepeatedPermutations stages.length p)
    (hrow : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, true))))) =
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e)
    (hcol : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, true))))) =
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e) :
    (∀ (edge : Fin 3 × Fin n) (network : Bool),
      let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
      let radius := last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j
      let initialGap := fwPhysicalEdgeTraceGap grown (fwSeedEdgeCells sr sc hsr hsc edge network)
        (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network)
      CompleteEvenGrid
        ((Finset.univ : Finset (Sum (Fin 16) (Fin stages.length))).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
          (Finset.range 5).image (Sum.inr : ℕ → Sum (Sum (Fin 16) (Fin stages.length)) ℕ))
        (joinedBridgeGap initialGap batches index) radius ∧
      (poolMaximum n : ℝ) ≤ radius ∧
      (∀ j : Fin 5, entry grown (fwBridgeLayerCells rows cols hr hc ((j, edge), (network, true))) =
        entry grown (fwBridgeLayerCells rows cols hr hc ((j, edge), (network, false))) +
          selectedBridgeGap batches index j)) ∧
    (∀ (j : Fin 5) (k : Fin 3) (e : Fin n),
      (rows.get (bridgeStageLayerIndex hr j k)).1 e = p k e ∧
      (cols.get (bridgeStageLayerIndex hc j k)).1 e = p k e) ∧
    (∀ (j : Fin 16) (k : Fin 3) (e : Fin n),
      (sr.get (bridgeStageLayerIndex hsr j k)).1 e = p k e ∧
      (sc.get (bridgeStageLayerIndex hsc j k)).1 e = p k e) ∧
    (∀ (j : Fin stages.length) (k : Fin 3) (e : Fin n),
      (gr.get (bridgeStageLayerIndex hgr j k)).1 e = p k e ∧
      (gc.get (bridgeStageLayerIndex hgc j k)).1 e = p k e) := by
  have hseedfixed : ∀ x, entry grown (fwSeedOrdinaryCells sr sc hsr hsc x) =
      entry old (fwSeedOrdinaryCells sr sc hsr hsc x) := by
    intro x
    apply hfixed
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)))
  obtain ⟨hgrid, heven, hseedmap, hgrowthmap⟩ :=
    fw_physical_edge_witness_trace_grid p batches candidates hcard kept hsub hkept hav sr sc hsr hsc
      hsrmap hscmap old grown hseedfixed hso trace offset hoff hs choice gr gc hgr hgc
      hgrmap hgcmap hrow hcol
  refine ⟨?_, ?_, hseedmap, hgrowthmap⟩
  · intro edge network
    exact fw_physical_bridge_extends_grid batches hvalid hrect hseed hwide hs choice rows cols hr hc
      sr sc hsr hsc wr wc hwr hwc old grown hfixed hplace edge network _ _ last
      (hgrid edge network) heven hcross
  · intro j k e
    exact ⟨bridgeStageLayer_endpoints rows hr p hrmap j k e,
      bridgeStageLayer_endpoints cols hc p hcmap j k e⟩

end
end Sude
