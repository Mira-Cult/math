import Sude.FWActualNetworkGapTotal
import Sude.FWPhysicalMidpointInvoice
import Sude.FWReallocatedSeedEdgeGap

/-! Physical midpoint comparison for a fresh reference over a reallocated
square. Every installation, preserved role, block and invoice is supplied;
no line-to-mean estimate or target existence is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

theorem fw_reallocated_reference_physical_midpoints {n L Q : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n))
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (old grown b b₀ : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hplace : ∀ x, entry old (fwBridgeLayerCells br bc hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (hbridge : ∀ x, entry b (fwBridgeLayerCells br bc hr hc x) = entry grown (fwBridgeLayerCells br bc hr hc x))
    (hwidePreserved : ∀ x : FWWideInputs n,
      entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) = entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x))
    (hseedNew : ∀ j i, entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i), true)) =
      entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i), false)) + 2)
    {initial final : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 Q initial 32 final last stages)
    (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (hgrowthPreserved : ∀ (edge : Fin 3 × Fin n) (network : Bool) i side,
      entry b (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network i side) =
      entry grown (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network i side))
    (hgrowthOld : ∀ (edge : Fin 3 × Fin n) (network : Bool) i,
      entry grown (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network i true) =
      entry grown (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network i false) +
        (BTStageTrace.stageAt stages rfl i).gap)
    (wide : (Fin 3 × Fin n) → Fin (3 * (n / 450)) → ℕ)
    (hwideOld : ∀ (edge : Fin 3 × Fin n) (j : Fin (3 * (n / 450))) (network : Bool),
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide edge j)
    (rect : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    (hrowGap : ∀ i e, entry b (((((br ++ sr) ++ wr) ++ gr).get i).1 e,
        ((((br ++ sr) ++ wr) ++ gr).get i).2 e) =
      entry b (e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) +
        fwPhysicalRowLayerGap b (((br ++ sr) ++ wr) ++ gr) i e)
    (hcolGap : ∀ i e, entry b (((((bc ++ sc) ++ wc) ++ gc).get i).2 e,
        ((((bc ++ sc) ++ wc) ++ gc).get i).1 e) =
      entry b (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, e) +
        fwPhysicalColumnLayerGap b (((bc ++ sc) ++ wc) ++ gc) i e)
    (BR : CenteredNetwork (Fin 3 × Fin n) (Fin ((((br ++ sr) ++ wr) ++ gr).length) × Fin n)
      (hrows.rowPairs b (fwPhysicalRowLayerGap b (((br ++ sr) ++ wr) ++ gr)) hrowGap))
    (BC : CenteredNetwork (Fin 3 × Fin n) (Fin ((((bc ++ sc) ++ wc) ++ gc).length) × Fin n)
      (hcols.columnPairs b (fwPhysicalColumnLayerGap b (((bc ++ sc) ++ wc) ++ gc)) hcolGap))
    (hends : ∀ e, BR.source e = e.2 ∧ BC.source e = e.2 ∧
      BR.target e = p e.1 e.2 ∧ BC.target e = p e.1 e.2)
    (hblockR : ∀ edge, BR.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)))
    (hblockC : ∀ edge, BC.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)))
    (hradius : ∀ edge, BR.radius edge = last +
      (∑ j ∈ Finset.range 5, selectedBridgeGap batches
        (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge) j) + ∑ j, wide edge j)
    (hsame : ∀ edge, BC.radius edge = BR.radius edge)
    (hinvoice : TwoNetworkReferenceInvoice b b₀ (((br ++ sr) ++ wr) ++ gr) (((bc ++ sc) ++ wc) ++ gc)
      hrows hcols (fwPhysicalRowLayerGap b (((br ++ sr) ++ wr) ++ gr))
      (fwPhysicalColumnLayerGap b (((bc ++ sc) ++ wc) ++ gc)) hrowGap hcolGap BR BC) :
    (∀ r, |2 * (rowSum b₀ r : ℤ) -
      physicalNetworkMidpointTwice (hrows.rowPairs b (fwPhysicalRowLayerGap b (((br ++ sr) ++ wr) ++ gr)) hrowGap) BR r| ≤ 9) ∧
    (∀ c, |2 * (columnSum b₀ c : ℤ) -
      physicalNetworkMidpointTwice (hcols.columnPairs b (fwPhysicalColumnLayerGap b (((bc ++ sc) ++ wc) ++ gc)) hcolGap) BC c| ≤ 9) := by
  have hbplace : ∀ x, entry b (fwBridgeLayerCells br bc hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x) := by
    intro x
    rw [hbridge x, hfixed]
    · exact hplace x
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have htotals : ∀ edge,
      (∑ k ∈ BR.block edge, (hrows.rowPairs b (fwPhysicalRowLayerGap b (((br ++ sr) ++ wr) ++ gr)) hrowGap).gap k) = BR.radius edge ∧
      (∑ k ∈ BC.block edge, (hcols.columnPairs b (fwPhysicalColumnLayerGap b (((bc ++ sc) ++ wc) ++ gc)) hcolGap).gap k) = BC.radius edge := by
    intro edge
    have hw : ∀ j network,
        entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
        entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide edge j := by
      intro j network
      rw [hwidePreserved, hwidePreserved]
      exact hwideOld edge j network
    have hg : ∀ network i,
        entry b (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network i true) =
        entry b (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network i false) +
          (BTStageTrace.stageAt stages rfl i).gap := by
      intro network i
      rw [hgrowthPreserved, hgrowthPreserved]
      exact hgrowthOld edge network i
    exact fw_actual_network_block_gap_totals batches hvalid hrect hseed hwide hs choice
      br bc hr hc sr sc hsr hsc wr wc hwr hwc b b (fun _ _ => rfl) hbplace
      trace offset hoff gr gc hgr hgc edge (wide edge) hw
      (fun network i => fw_reallocated_seed_edge_gap hseed hs choice sr sc hsr hsc b hseedNew edge network i)
      hg rect hrows hcols hrowGap hcolGap BR BC (hblockR edge) (hblockC edge) (hradius edge) (hsame edge)
  exact fw_reference_invoice_physical_midpoint_bounds p b b₀ rect
    (((br ++ sr) ++ wr) ++ gr) (((bc ++ sc) ++ wc) ++ gc) hrows hcols
    (fwPhysicalRowLayerGap b (((br ++ sr) ++ wr) ++ gr))
    (fwPhysicalColumnLayerGap b (((bc ++ sc) ++ wc) ++ gc)) hrowGap hcolGap BR BC hends
    (fun e => (htotals e).1) (fun e => (htotals e).2) hinvoice

end
end Sude
