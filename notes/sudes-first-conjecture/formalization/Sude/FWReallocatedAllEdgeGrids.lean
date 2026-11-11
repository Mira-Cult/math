import Sude.FWReallocatedActualEdgeGrid
import Sude.FWReallocatedSeedEdgeGap
import Sude.FWJointSupportedCellSeparation
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
/-- Reconstruct all edge grids on one reallocated square; independent packed geometry gives global endpoint separation. -/
theorem fw_reallocated_actual_all_edge_grids {n L : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n))
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (hrmap : br.map Prod.fst = bridgeRepeatedPermutations 5 p)
    (hcmap : bc.map Prod.fst = bridgeRepeatedPermutations 5 p)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hsrmap : sr.map Prod.fst = bridgeRepeatedPermutations 16 p)
    (hscmap : sc.map Prod.fst = bridgeRepeatedPermutations 16 p)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (old grown b : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hplace : ∀ x, entry old (fwBridgeLayerCells br bc hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    {stages : List BTSelectedStage} (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (hgrmap : gr.map Prod.fst = bridgeRepeatedPermutations stages.length p)
    (hgcmap : gc.map Prod.fst = bridgeRepeatedPermutations stages.length p)
    (hwidecoords : ∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (side : Bool),
      fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e false side) =
        ((if side then p k e else e), (wr.get (bridgeStageLayerIndex hwr j k)).2 e) ∧
      fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e true side) =
        ((wc.get (bridgeStageLayerIndex hwc j k)).2 e, (if side then p k e else e)))
    (wide : (Fin 3 × Fin n) → Fin (3 * (n / 450)) → ℕ) (R : (Fin 3 × Fin n) → ℕ)
    (hwidepair : ∀ (edge : Fin 3 × Fin n) (j : Fin (3 * (n / 450))) (network : Bool),
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide edge j)
    (hbridgePreserved : ∀ x, entry b (fwBridgeLayerCells br bc hr hc x) = entry grown (fwBridgeLayerCells br bc hr hc x))
    (hwidePreserved : ∀ x : FWWideInputs n,
      entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) = entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x))
    (hseedOld : ∀ (edge : Fin 3 × Fin n) (network : Bool) (j : Fin 16),
      entry grown (fwSeedEdgeCells sr sc hsr hsc edge network j true) =
      entry grown (fwSeedEdgeCells sr sc hsr hsc edge network j false) + 2)
    (hseedNew : ∀ j i, entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i), true)) =
      entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i), false)) + 2)
    (hgrowth : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry b (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x))
    (rect : Finset (Cell n))
    (hrowPack : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcolPack : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    (hgrids : ∀ (edge : Fin 3 × Fin n) (network : Bool),
      let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
      let initialGap := fwPhysicalEdgeTraceGap grown (fwSeedEdgeCells sr sc hsr hsc edge network)
        (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network)
      CompleteEvenGrid (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450)))
        (Sum.elim (joinedBridgeGap initialGap batches index) (wide edge)) (R edge)) :
    (let α := ({t // t ∈ fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))} × Fin 3) × Fin n
     let rslot : α → Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n :=
       fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr
     let cslot : α → Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n :=
       fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc
     Function.Injective (fun x : α × Bool => layerPairSlot (((br ++ sr) ++ wr) ++ gr) (rslot x.1) x.2) ∧
     Function.Injective (fun x : α × Bool => (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (cslot x.1) x.2).swap) ∧
     (∀ x y : α × Bool, layerPairSlot (((br ++ sr) ++ wr) ++ gr) (rslot x.1) x.2 ≠
       (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (cslot y.1) y.2).swap) ∧
     (∀ x : α × Bool, layerPairSlot (((br ++ sr) ++ wr) ++ gr) (rslot x.1) x.2 ∉ rect) ∧
     (∀ x : α × Bool, (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (cslot x.1) x.2).swap ∉ rect)) ∧
    (∀ edge : Fin 3 × Fin n,
    let labels := fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))
    let rows := ((br ++ sr) ++ wr) ++ gr
    let cols := ((bc ++ sc) ++ wc) ++ gc
    let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
    let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
    CompleteEvenGrid (labels.attach.image rowSlot) (fun x => fwPhysicalRowLayerGap b rows x.1 x.2) (R edge) ∧
    CompleteEvenGrid (labels.attach.image colSlot) (fun x => fwPhysicalColumnLayerGap b cols x.1 x.2) (R edge) ∧
    (∀ x side, LayerPacking.sequenceCell rows ((rowSlot x).1, ((rowSlot x).2, side)) =
      ((if side then p edge.1 edge.2 else edge.2), (rows.get (rowSlot x).1).2 edge.2)) ∧
    (∀ x side, (LayerPacking.sequenceCell cols ((colSlot x).1, ((colSlot x).2, side))).swap =
      ((cols.get (colSlot x).1).2 edge.2, (if side then p edge.1 edge.2 else edge.2)))) := by
  constructor
  · exact fw_joint_actual_supported_cells_separate rect br bc sr sc wr wc gr gc
      hr hc hsr hsc hwr hwc hgr hgc hrowPack hcolPack
  intro edge
  apply fw_reallocated_actual_edge_joint_grids p batches hvalid hrect hseed hwide hs choice
    br bc hr hc hrmap hcmap sr sc hsr hsc hsrmap hscmap wr wc hwr hwc old grown b hfixed hplace
    offset hoff gr gc hgr hgc hgrmap hgcmap hwidecoords edge (wide edge) (R edge)
    (hwidepair edge) hbridgePreserved hwidePreserved (hseedOld edge)
  · intro network j
    exact fw_reallocated_seed_edge_gap hseed hs choice sr sc hsr hsc b hseedNew edge network j
  · intro network j side
    cases network
    · exact hgrowth (Sum.inr (Sum.inl (finProdFinEquiv (j,edge.1), (edge.2,side))))
    · exact hgrowth (Sum.inr (Sum.inr (finProdFinEquiv (j,edge.1), (edge.2,side))))
  · exact hgrids edge

end
end Sude
