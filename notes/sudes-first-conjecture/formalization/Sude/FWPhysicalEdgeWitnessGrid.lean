import Sude.FWPhysicalEdgeTraceGrid
import Sude.FWEarlyGrowthPhysical

/-! Per-edge grids of actual physical entry differences for supplied early
and growth installation witnesses. This does not assert pairwise spatial
disjointness, threshold crossing, bridge coverage, or line sums. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- One ordinary physical seed pair at each retained stage and fixed graph edge. -/
def fwSeedEdgeCells {n : ℕ} (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (edge : Fin 3 × Fin n) (network : Bool) (j : Fin 16) (side : Bool) : Cell n :=
  if network then fwSeedOrdinaryCells sr sc hsr hsc
    (Sum.inr (finProdFinEquiv (j, edge.1), (edge.2, side)))
  else fwSeedOrdinaryCells sr sc hsr hsc
    (Sum.inl (finProdFinEquiv (j, edge.1), (edge.2, side)))

/-- The physical growth pair for the same graph edge and one trace stage. -/
def fwGrowthEdgeCells {n L P : ℕ} (offset : ℕ)
    (hoff : offset + P * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (edge : Fin 3 × Fin n) (network : Bool) (j : Fin P) (side : Bool) : Cell n :=
  if network then btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc
    (Sum.inr (Sum.inr (finProdFinEquiv (j, edge.1), (edge.2, side))))
  else btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc
    (Sum.inr (Sum.inl (finProdFinEquiv (j, edge.1), (edge.2, side))))

/-- The installed retained-seed endpoint equations give gap two on either
ordinary graph network after its physical cells are preserved. -/
theorem fw_seed_edge_gap_after_preservation {n : ℕ}
    (batches : ℕ → List DoublePair)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hav : ∀ x, sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard x ∈
      poolFinset n \ priorBridgeReservation ∅ (Finset.range 5) batches)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ x, entry grown (fwSeedOrdinaryCells sr sc hsr hsc x) =
      entry old (fwSeedOrdinaryCells sr sc hsr hsc x))
    (hso : ∀ x, entry old (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x)))
    (edge : Fin 3 × Fin n) (network : Bool) (j : Fin 16) :
    entry grown (fwSeedEdgeCells sr sc hsr hsc edge network j true) =
      entry grown (fwSeedEdgeCells sr sc hsr hsc edge network j false) + 2 := by
  cases network
  · change entry grown (fwSeedOrdinaryCells sr sc hsr hsc (Sum.inl (finProdFinEquiv (j, edge.1), (edge.2, true)))) =
      entry grown (fwSeedOrdinaryCells sr sc hsr hsc (Sum.inl (finProdFinEquiv (j, edge.1), (edge.2, false)))) + 2
    rw [hfixed, hfixed, hso, hso]
    simpa [fwSeedOrdinaryInput, prefixNetworkInput, prefixOrdinaryInput, retainedSeedPoolValues] using
      retainedSeedPoolValues_gap candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept
        (priorBridgeReservation ∅ (Finset.range 5) batches) hav j
        (prefixOrdinaryPairIndex (d := 6) (r := 3) (n := n) (by omega) (0, edge))
  · change entry grown (fwSeedOrdinaryCells sr sc hsr hsc (Sum.inr (finProdFinEquiv (j, edge.1), (edge.2, true)))) =
      entry grown (fwSeedOrdinaryCells sr sc hsr hsc (Sum.inr (finProdFinEquiv (j, edge.1), (edge.2, false)))) + 2
    rw [hfixed, hfixed, hso, hso]
    simpa [fwSeedOrdinaryInput, prefixNetworkInput, prefixOrdinaryInput, retainedSeedPoolValues] using
      retainedSeedPoolValues_gap candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept
        (priorBridgeReservation ∅ (Finset.range 5) batches) hav j
        (prefixOrdinaryPairIndex (d := 6) (r := 3) (n := n) (by omega) (1, edge))

/-- The growth stage's ordinary pair at a fixed graph edge has that exact
trace-stage gap, on either network. -/
theorem fw_growth_edge_gap_of_installation {n L : ℕ}
    {stages : List BTSelectedStage}
    (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3)
    (hgc : gc.length = stages.length * 3) (grown : Cell n ≃ Fin (n*n))
    (hrow : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, true))))) =
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e)
    (hcol : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, true))))) =
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e)
    (edge : Fin 3 × Fin n) (network : Bool) (j : Fin stages.length) :
    entry grown (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network j true) =
      entry grown (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network j false) +
        (BTStageTrace.stageAt stages rfl j).gap := by
  cases network
  · change entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc
        (Sum.inr (Sum.inl (finProdFinEquiv (j, edge.1), (edge.2, true))))) =
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc
        (Sum.inr (Sum.inl (finProdFinEquiv (j, edge.1), (edge.2, false))))) + _
    simpa [variablePrefixNetworkGap] using hrow (finProdFinEquiv (j, edge.1)) edge.2
  · change entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc
        (Sum.inr (Sum.inr (finProdFinEquiv (j, edge.1), (edge.2, true))))) =
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc
        (Sum.inr (Sum.inr (finProdFinEquiv (j, edge.1), (edge.2, false))))) + _
    simpa [variablePrefixNetworkGap] using hcol (finProdFinEquiv (j, edge.1)) edge.2

/-- For every graph edge and each orientation, the actual retained-seed
pairs and installed trace pairs form an even grid through the exact final
trace radius. The supplied layer maps identify both families with the same
permutation triple; physical pairwise switch separation is not asserted. -/
theorem fw_physical_edge_witness_trace_grid {n L : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n)) (batches : ℕ → List DoublePair)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hav : ∀ x, sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard x ∈
      poolFinset n \ priorBridgeReservation ∅ (Finset.range 5) batches)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hsrmap : sr.map Prod.fst = bridgeRepeatedPermutations 16 p)
    (hscmap : sc.map Prod.fst = bridgeRepeatedPermutations 16 p)
    (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ x, entry grown (fwSeedOrdinaryCells sr sc hsr hsc x) =
      entry old (fwSeedOrdinaryCells sr sc hsr hsc x))
    (hso : ∀ x, entry old (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x)))
    {initial final : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last stages)
    (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
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
      CompleteEvenGrid (Finset.univ : Finset (Sum (Fin 16) (Fin stages.length)))
        (fwPhysicalEdgeTraceGap grown (fwSeedEdgeCells sr sc hsr hsc edge network)
          (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network)) last) ∧
    2 ∣ last ∧
    (∀ (j : Fin 16) (k : Fin 3) (e : Fin n),
      (sr.get (bridgeStageLayerIndex hsr j k)).1 e = p k e ∧
      (sc.get (bridgeStageLayerIndex hsc j k)).1 e = p k e) ∧
    (∀ (j : Fin stages.length) (k : Fin 3) (e : Fin n),
      (gr.get (bridgeStageLayerIndex hgr j k)).1 e = p k e ∧
      (gc.get (bridgeStageLayerIndex hgc j k)).1 e = p k e) := by
  have hresult (edge : Fin 3 × Fin n) (network : Bool) :=
    fw_physical_edge_trace_grid grown trace (fwSeedEdgeCells sr sc hsr hsc edge network)
      (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network)
      (fw_seed_edge_gap_after_preservation batches candidates hcard kept hsub hkept hav sr sc hsr hsc
        old grown hfixed hso edge network)
      (fw_growth_edge_gap_of_installation offset hoff hs choice gr gc hgr hgc grown hrow hcol edge network)
  refine ⟨fun edge network => (hresult edge network).1, ?_, ?_, ?_⟩
  · have hsum : 2 ∣ (stages.map BTSelectedStage.gap).sum := by
      apply List.dvd_sum
      intro x hx
      obtain ⟨stage, hs, rfl⟩ := List.mem_map.mp hx
      exact (trace.stage_properties stage hs).2.1
    rw [trace.final_accounting.2.2]
    exact dvd_add (by decide) hsum
  · intro j k e
    exact ⟨bridgeStageLayer_endpoints sr hsr p hsrmap j k e,
      bridgeStageLayer_endpoints sc hsc p hscmap j k e⟩
  · intro j k e
    exact ⟨bridgeStageLayer_endpoints gr hgr p hgrmap j k e,
      bridgeStageLayer_endpoints gc hgc p hgcmap j k e⟩

end
end Sude
