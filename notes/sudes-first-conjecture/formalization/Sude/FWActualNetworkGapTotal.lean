import Sude.FWActualJointGapTotal
import Sude.FWActualStrongWideInvoice

/-! Relate supplied physical accounting to the exact same centered-network
blocks and radii. The physical trace, pair identities and block/radius
identities remain explicit hypotheses. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

theorem fw_actual_network_block_gap_totals {n L Q : ℕ}
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hplace : ∀ x, entry old (fwBridgeLayerCells br bc hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    {initial final : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 Q initial 32 final last stages)
    (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (edge : Fin 3 × Fin n) (wide : Fin (3 * (n / 450)) → ℕ)
    (hwidepair : ∀ (j : Fin (3 * (n / 450))) (network : Bool),
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide j)
    (hseedpair : ∀ network i,
      entry grown (fwSeedEdgeCells sr sc hsr hsc edge network i true) =
      entry grown (fwSeedEdgeCells sr sc hsr hsc edge network i false) + 2)
    (hgrowthpair : ∀ network i,
      entry grown (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network i true) =
      entry grown (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network i false) +
        (BTStageTrace.stageAt stages rfl i).gap)
    (rect : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    (hrowGap : ∀ i e, entry grown (((((br ++ sr) ++ wr) ++ gr).get i).1 e,
        ((((br ++ sr) ++ wr) ++ gr).get i).2 e) =
      entry grown (e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) +
        fwPhysicalRowLayerGap grown (((br ++ sr) ++ wr) ++ gr) i e)
    (hcolGap : ∀ i e, entry grown (((((bc ++ sc) ++ wc) ++ gc).get i).2 e,
        ((((bc ++ sc) ++ wc) ++ gc).get i).1 e) =
      entry grown (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, e) +
        fwPhysicalColumnLayerGap grown (((bc ++ sc) ++ wc) ++ gc) i e)
    (BR : CenteredNetwork (Fin 3 × Fin n) (Fin ((((br ++ sr) ++ wr) ++ gr).length) × Fin n)
      (hrows.rowPairs grown (fwPhysicalRowLayerGap grown (((br ++ sr) ++ wr) ++ gr)) hrowGap))
    (BC : CenteredNetwork (Fin 3 × Fin n) (Fin ((((bc ++ sc) ++ wc) ++ gc).length) × Fin n)
      (hcols.columnPairs grown (fwPhysicalColumnLayerGap grown (((bc ++ sc) ++ wc) ++ gc)) hcolGap))
    (hblockR : BR.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)))
    (hblockC : BC.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)))
    (hradius : BR.radius edge = last +
      (∑ j ∈ Finset.range 5, selectedBridgeGap batches
        (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge) j) + ∑ j, wide j)
    (hsame : BC.radius edge = BR.radius edge) :
    (∑ k ∈ BR.block edge, (hrows.rowPairs grown
      (fwPhysicalRowLayerGap grown (((br ++ sr) ++ wr) ++ gr)) hrowGap).gap k) = BR.radius edge ∧
    (∑ k ∈ BC.block edge, (hcols.columnPairs grown
      (fwPhysicalColumnLayerGap grown (((bc ++ sc) ++ wc) ++ gc)) hcolGap).gap k) = BC.radius edge := by
  obtain ⟨hR, hC⟩ := fw_actual_joint_grid_gap_totals batches hvalid hrect hseed hwide hs choice
    br bc hr hc sr sc hsr hsc wr wc hwr hwc old grown hfixed hplace trace offset hoff gr gc hgr hgc
    edge wide hwidepair hseedpair hgrowthpair
  constructor
  · rw [hblockR, hradius]
    exact hR
  · rw [hblockC, hsame, hradius]
    exact hC

end
end Sude
