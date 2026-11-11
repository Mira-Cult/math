import Sude.FWReallocatedReconciledInvoice
import Sude.FWSeedReallocationRolePreservation

/-! Preserve supplied same-square evidence while constructing a fresh invoice after seed reallocation. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

theorem fw_packed_reallocated_concentration_new_invoice {n L : ℕ}
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
    {stages : List BTSelectedStage} (hoff : (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) + stages.length * (4 * 6) ≤ L)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (hgrmap : gr.map Prod.fst = bridgeRepeatedPermutations stages.length p)
    (hgcmap : gc.map Prod.fst = bridgeRepeatedPermutations stages.length p)
    (hwidecoords : ∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (side : Bool),
      fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e false side) =
        ((if side then p k e else e), (wr.get (bridgeStageLayerIndex hwr j k)).2 e) ∧
      fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e true side) =
        ((wc.get (bridgeStageLayerIndex hwc j k)).2 e, (if side then p k e else e)))
    (last : ℕ)
    (hseedOld : ∀ (edge : Fin 3 × Fin n) (network : Bool) (j : Fin 16),
      entry grown (fwSeedEdgeCells sr sc hsr hsc edge network j true) =
      entry grown (fwSeedEdgeCells sr sc hsr hsc edge network j false) + 2)
    (hseedNew : ∀ j i, entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i), true)) =
      entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i), false)) + 2)
    (C : (Cell n ≃ Fin (n*n)) → Prop) (hC : C b)
    (hseedFixed : ∀ c, c ∉ Set.range (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) →
      entry b c = entry grown c)
    (hbrPack : LayerPacking.PackedLayers (packedRectangleSupport hs choice) br)
    (hbcPack : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br)) bc)
    (hsrPack : LayerPacking.PackedLayers
      ((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport bc)) sr)
    (hscPack : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪ LayerPacking.layersSupport sr)) sc)
    (hsdisj : Disjoint (LayerPacking.layersSupport sr) (LayerPacking.transposeCells (LayerPacking.layersSupport sc)))
    (hwrPack : LayerPacking.PackedLayers
      ((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪ LayerPacking.layersSupport sr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport sc)) wr)
    (hwcPack : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪ LayerPacking.layersSupport sr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪ LayerPacking.layersSupport wr)) wc)
    (hgrPack : LayerPacking.PackedLayers (fwGrowthEarlyBase hs choice br bc sr sc wr wc) gr)
    (hgcPack : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (fwGrowthEarlyBase hs choice br bc sr sc wr wc ∪ LayerPacking.layersSupport gr)) gc)
    (hgdisj : Disjoint (LayerPacking.layersSupport gr) (LayerPacking.transposeCells (LayerPacking.layersSupport gc)))
    (rect : Finset (Cell n))
    (hrowPack : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcolPack : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    (hrowOld : ∀ i e, entry grown (((((br ++ sr) ++ wr) ++ gr).get i).1 e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) =
      entry grown (e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) + fwPhysicalRowLayerGap grown (((br ++ sr) ++ wr) ++ gr) i e)
    (hcolOld : ∀ i e, entry grown (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, ((((bc ++ sc) ++ wc) ++ gc).get i).1 e) =
      entry grown (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, e) + fwPhysicalColumnLayerGap grown (((bc ++ sc) ++ wc) ++ gc) i e)
    (hwidegrid : ∀ (edge : Fin 3 × Fin n) (network : Bool),
      let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
      let radius := last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j
      let initialGap := fwPhysicalEdgeTraceGap grown (fwSeedEdgeCells sr sc hsr hsc edge network)
        (fwGrowthEdgeCells (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc edge network)
      let base := fwJointPreWideGridLabels stages.length
      ∃ wide : Fin (3 * (n / 450)) → ℕ,
        (∀ j, 0 < wide j ∧ 2 ∣ wide j ∧
          (∀ sideNetwork : Bool,
            entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 sideNetwork true)) =
            entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 sideNetwork false)) + wide j) ∧
          (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (wide j : ℝ) ∧ (wide j : ℝ) < poolMaximum n) ∧
        CompleteEvenGrid (fwJointGridLabels base (3 * (n / 450)))
          (Sum.elim (joinedBridgeGap initialGap batches index) wide) (radius + ∑ j, wide j) ∧
        2 ∣ radius + ∑ j, wide j ∧
        (2 : ℝ) * (n / 450 : ℕ) * (poolMaximum n : ℝ) ≤ ∑ j, (wide j : ℝ)) :
    C b ∧
    (∀ t side, entry b (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      entry grown (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side))) ∧
    (∀ x, entry b (fwBridgeLayerCells br bc hr hc x) = entry grown (fwBridgeLayerCells br bc hr hc x)) ∧
    (∀ x : FWWideInputs n, entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x)) ∧
    (∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry b (btGrowingOffsetCells (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc x) =
      entry grown (btGrowingOffsetCells (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc x)) ∧
    ∃ wide : (Fin 3 × Fin n) → Fin (3 * (n / 450)) → ℕ,
    (∀ edge,
      (∀ j, 0 < wide edge j ∧ 2 ∣ wide edge j ∧
        (∀ network : Bool,
          entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
          entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide edge j) ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (wide edge j : ℝ) ∧ (wide edge j : ℝ) < poolMaximum n) ∧
      (∀ (j : Fin (3 * (n / 450))) (network : Bool),
        entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
        entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide edge j) ∧
      2 ∣ (last + (∑ j ∈ Finset.range 5, selectedBridgeGap batches
        (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge) j) + ∑ j, wide edge j) ∧
      (2 : ℝ) * (n / 450 : ℕ) * (poolMaximum n : ℝ) ≤ ∑ j, (wide edge j : ℝ)) ∧
    (let N := (n / 450) * poolMaximum n
    let source : Fin 3 × Fin n → Fin n := fun e => e.2
    let target : Fin 3 × Fin n → Fin n := fun e => p e.1 e.2
    let rowLayers := ((br ++ sr) ++ wr) ++ gr
    let colLayers := ((bc ++ sc) ++ wc) ++ gc
    let rowGap := fwPhysicalRowLayerGap b rowLayers
    let colGap := fwPhysicalColumnLayerGap b colLayers
    ∃ (hrowNew : ∀ i e, entry b ((rowLayers.get i).1 e, (rowLayers.get i).2 e) =
          entry b (e, (rowLayers.get i).2 e) + rowGap i e)
      (hcolNew : ∀ i e, entry b ((colLayers.get i).2 e, (colLayers.get i).1 e) =
          entry b ((colLayers.get i).2 e, e) + colGap i e)
      (BR : CenteredNetwork (Fin 3 × Fin n) (Fin rowLayers.length × Fin n)
        (hrowPack.rowPairs b rowGap hrowNew))
      (BC : CenteredNetwork (Fin 3 × Fin n) (Fin colLayers.length × Fin n)
        (hcolPack.columnPairs b colGap hcolNew))
      (b₀ : Cell n ≃ Fin (n*n)),
      TwoNetworkReferenceInvoice b b₀ rowLayers colLayers hrowPack hcolPack rowGap colGap
        hrowNew hcolNew BR BC ∧
      (∀ edge, BR.source edge = edge.2 ∧ BC.source edge = edge.2 ∧
        BR.target edge = p edge.1 edge.2 ∧ BC.target edge = p edge.1 edge.2) ∧
      (∀ edge, BR.block edge =
        (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
          (fun x => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2))) ∧
      (∀ edge, BC.block edge =
        (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
          (fun x => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2))) ∧
      (∀ edge, BR.radius edge = last +
        (∑ j ∈ Finset.range 5, selectedBridgeGap batches
          (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge) j) + ∑ j, wide edge j) ∧
      (∀ edge, BC.radius edge = BR.radius edge) ∧
      (∀ edge, 2 * N ≤ BR.radius edge) ∧
      mainSum b₀ = mainSum b ∧ antiSum b₀ = antiSum b ∧
      (∀ c ∈ rect, entry b₀ c = entry b c) ∧
      ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ out : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum out r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fr e r) ∧
        (∀ c, (columnSum out c : ℤ) - (columnSum b₀ c : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fc e c) ∧
        mainSum out = mainSum b₀ ∧ antiSum out = antiSum b₀ ∧
        (∀ c ∈ rect, entry out c = entry b₀ c) ∧
        Set.range (entry out) = pool n ∧ Function.Injective (entry out)) := by
  obtain ⟨hbridgeRect, hbridgePreserved, hwidePreserved, hgrowthPreserved⟩ :=
    fw_seed_reallocation_preserves_other_roles hrect hseed hwide hoff hs choice br bc hr hc
      hbrPack hbcPack sr sc hsr hsc hsrPack hscPack hsdisj wr wc hwr hwc hwrPack hwcPack
      gr gc hgr hgc hgrPack hgcPack hgdisj grown b hseedFixed
  refine ⟨hC, hbridgeRect, hbridgePreserved, hwidePreserved, hgrowthPreserved, ?_⟩
  exact fw_reallocated_reconciled_grids_new_invoice p batches hvalid hrect hseed hwide hs choice
    br bc hr hc hrmap hcmap sr sc hsr hsc hsrmap hscmap wr wc hwr hwc old grown b hfixed hplace
    (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff gr gc hgr hgc hgrmap hgcmap hwidecoords last hbridgePreserved hwidePreserved
    hseedOld hseedNew hgrowthPreserved rect hrowPack hcolPack hrowOld hcolOld hwidegrid

end
end Sude
