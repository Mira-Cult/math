import Sude.FWReallocatedAllEdgeGrids
import Sude.FWReallocatedOrientation
import Sude.FWActualExplicitWideInvoice

/-! Construct a new invoice and flow reference on the seed-reallocated square. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

theorem fw_reallocated_actual_grids_new_invoice {n L : ℕ}
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
    (wide : (Fin 3 × Fin n) → Fin (3 * (n / 450)) → ℕ) (R : (Fin 3 × Fin n) → ℕ) (last : ℕ)
    (hR : ∀ edge, R edge = last +
      (∑ j ∈ Finset.range 5, selectedBridgeGap batches
        (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge) j) + ∑ j, wide edge j)
    (hwideSum : ∀ edge, (2 : ℝ) * (n / 450 : ℕ) * (poolMaximum n : ℝ) ≤ ∑ j, (wide edge j : ℝ))
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
    (hrowOld : ∀ i e, entry grown (((((br ++ sr) ++ wr) ++ gr).get i).1 e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) =
      entry grown (e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) + fwPhysicalRowLayerGap grown (((br ++ sr) ++ wr) ++ gr) i e)
    (hcolOld : ∀ i e, entry grown (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, ((((bc ++ sc) ++ wc) ++ gc).get i).1 e) =
      entry grown (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, e) + fwPhysicalColumnLayerGap grown (((bc ++ sc) ++ wc) ++ gc) i e)
    (hgrids : ∀ (edge : Fin 3 × Fin n) (network : Bool),
      let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
      let initialGap := fwPhysicalEdgeTraceGap grown (fwSeedEdgeCells sr sc hsr hsc edge network)
        (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network)
      CompleteEvenGrid (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450)))
        (Sum.elim (joinedBridgeGap initialGap batches index) (wide edge)) (R edge)) :
    let N := (n / 450) * poolMaximum n
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
        Set.range (entry out) = pool n ∧ Function.Injective (entry out) := by
  obtain ⟨hrowNew, hcolNew⟩ := fw_joint_gap_equations_after_seed_reallocation_of_joint_gaps
    hseed hwide offset hoff hs choice br bc sr sc wr wc gr gc hr hc hsr hsc hwr hwc hgr hgc
    grown b hrowOld hcolOld hseedNew hbridgePreserved hwidePreserved hgrowth
  obtain ⟨_, hactual⟩ := fw_reallocated_actual_all_edge_grids p batches hvalid hrect hseed hwide hs choice
    br bc hr hc hrmap hcmap sr sc hsr hsc hsrmap hscmap wr wc hwr hwc old grown b hfixed hplace
    offset hoff gr gc hgr hgc hgrmap hgcmap hwidecoords wide R hwidepair hbridgePreserved hwidePreserved
    hseedOld hseedNew hgrowth rect hrowPack hcolPack hgrids
  have hnewgrids : ∀ edge : Fin 3 × Fin n,
      let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
      let radius := last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j
      let labels := fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))
      let rows := ((br ++ sr) ++ wr) ++ gr
      let cols := ((bc ++ sc) ++ wc) ++ gc
      let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
      let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
      CompleteEvenGrid (labels.attach.image rowSlot) (fun x => fwPhysicalRowLayerGap b rows x.1 x.2)
          (radius + ∑ j, wide edge j) ∧
        CompleteEvenGrid (labels.attach.image colSlot) (fun x => fwPhysicalColumnLayerGap b cols x.1 x.2)
          (radius + ∑ j, wide edge j) ∧
        (∀ x side, LayerPacking.sequenceCell rows ((rowSlot x).1, ((rowSlot x).2, side)) =
          ((if side then p edge.1 edge.2 else edge.2), (rows.get (rowSlot x).1).2 edge.2)) ∧
        (∀ x side, (LayerPacking.sequenceCell cols ((colSlot x).1, ((colSlot x).2, side))).swap =
          ((cols.get (colSlot x).1).2 edge.2, (if side then p edge.1 edge.2 else edge.2))) ∧
        (2 : ℝ) * (n / 450 : ℕ) * (poolMaximum n : ℝ) ≤ ∑ j, (wide edge j : ℝ) := by
    intro edge
    have h := hactual edge
    dsimp only at h ⊢
    rw [hR edge] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hwideSum edge⟩
  refine ⟨hrowNew, hcolNew, ?_⟩
  exact fw_actual_grids_realize_supplied_flows_with_explicit_wide_invoice b rect p batches last
    br bc sr sc wr wc gr gc hr hc hsr hsc hwr hwc hgr hgc hrowPack hcolPack hrowNew hcolNew wide hnewgrids

end
end Sude
