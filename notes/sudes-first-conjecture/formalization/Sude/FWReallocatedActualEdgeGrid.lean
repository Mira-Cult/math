import Sude.FWReallocatedJoinedGrid
import Sude.FWReallocatedJointGap
import Sude.FWJointGraphEndpoints

/-! Reconstruct one edge's supplied row and column grids on a seed-reallocated
square. The same supplied wide gaps and grid radius are retained. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

theorem fw_reallocated_actual_edge_joint_grids {n L : ℕ}
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
    (edge : Fin 3 × Fin n) (wide : Fin (3 * (n / 450)) → ℕ) (R : ℕ)
    (hwidepair : ∀ (j : Fin (3 * (n / 450))) (network : Bool),
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide j)
    (hbridgePreserved : ∀ x, entry b (fwBridgeLayerCells br bc hr hc x) = entry grown (fwBridgeLayerCells br bc hr hc x))
    (hwidePreserved : ∀ x : FWWideInputs n,
      entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) = entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x))
    (hseedOld : ∀ (network : Bool) (j : Fin 16),
      entry grown (fwSeedEdgeCells sr sc hsr hsc edge network j true) =
      entry grown (fwSeedEdgeCells sr sc hsr hsc edge network j false) + 2)
    (hseedNew : ∀ (network : Bool) (j : Fin 16),
      entry b (fwSeedEdgeCells sr sc hsr hsc edge network j true) =
      entry b (fwSeedEdgeCells sr sc hsr hsc edge network j false) + 2)
    (hgrowth : ∀ (network : Bool) (j : Fin stages.length) (side : Bool),
      entry b (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network j side) =
      entry grown (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network j side))
    (hgrids : ∀ network : Bool,
      let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
      let initialGap := fwPhysicalEdgeTraceGap grown (fwSeedEdgeCells sr sc hsr hsc edge network)
        (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network)
      CompleteEvenGrid (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450)))
        (Sum.elim (joinedBridgeGap initialGap batches index) wide) R) :
    let labels := fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))
    let rows := ((br ++ sr) ++ wr) ++ gr
    let cols := ((bc ++ sc) ++ wc) ++ gc
    let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
    let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
    CompleteEvenGrid (labels.attach.image rowSlot) (fun x => fwPhysicalRowLayerGap b rows x.1 x.2) R ∧
    CompleteEvenGrid (labels.attach.image colSlot) (fun x => fwPhysicalColumnLayerGap b cols x.1 x.2) R ∧
    (∀ x side, LayerPacking.sequenceCell rows ((rowSlot x).1, ((rowSlot x).2, side)) =
      ((if side then p edge.1 edge.2 else edge.2), (rows.get (rowSlot x).1).2 edge.2)) ∧
    (∀ x side, (LayerPacking.sequenceCell cols ((colSlot x).1, ((colSlot x).2, side))).swap =
      ((cols.get (colSlot x).1).2 edge.2, (if side then p edge.1 edge.2 else edge.2))) := by
  dsimp only
  let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
  let base := fwJointPreWideGridLabels stages.length
  let rowGap := joinedBridgeGap (fwPhysicalEdgeTraceGap b (fwSeedEdgeCells sr sc hsr hsc edge false)
    (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge false)) batches index
  let colGap := joinedBridgeGap (fwPhysicalEdgeTraceGap b (fwSeedEdgeCells sr sc hsr hsc edge true)
    (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge true)) batches index
  let rows := ((br ++ sr) ++ wr) ++ gr
  let cols := ((bc ++ sc) ++ wc) ++ gc
  let labels := fwJointGridLabels base (3 * (n / 450))
  let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
  let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
  have hrowgrid : CompleteEvenGrid labels (Sum.elim rowGap wide) R := by
    exact fw_reallocated_joined_grid grown b _ _ (hseedOld false) (hseedNew false) (hgrowth false) batches index wide labels R (hgrids false)
  have hcolgrid : CompleteEvenGrid labels (Sum.elim colGap wide) R := by
    exact fw_reallocated_joined_grid grown b _ _ (hseedOld true) (hseedNew true) (hgrowth true) batches index wide labels R (hgrids true)
  have hrowinj : Function.Injective rowSlot := by
    intro x y heq
    have h := fwJointActualGridPairIndex_injective br sr wr gr hr hsr hwr hgr heq
    exact congrArg (fun z => z.1.1) h
  have hcolinj : Function.Injective colSlot := by
    intro x y heq
    have h := fwJointActualGridPairIndex_injective bc sc wc gc hc hsc hwc hgc heq
    exact congrArg (fun z => z.1.1) h
  obtain ⟨hrowgap, hcolgap⟩ := fw_joint_supported_gap_after_seed_reallocation batches hvalid hrect hseed hwide hs choice
    br bc hr hc sr sc hsr hsc wr wc hwr hwc old grown hfixed hplace offset hoff gr gc hgr hgc edge wide
    hwidepair b hbridgePreserved hwidePreserved
  have hwideends := fw_wide_layer_endpoints_of_physical_coordinates hwide hs choice wr wc hwr hwc p hwidecoords
  have hrowedge (x : {x // x ∈ labels}) : (rowSlot x).2 = edge.2 ∧ (rows.get (rowSlot x).1).1 edge.2 = p edge.1 edge.2 := by
    exact fw_joint_actual_grid_pair_graph br sr wr gr hr hsr hwr hgr p
      (bridgeStageLayer_endpoints br hr p hrmap) (bridgeStageLayer_endpoints sr hsr p hsrmap)
      (fun j k e => (hwideends j k e).1) (bridgeStageLayer_endpoints gr hgr p hgrmap) x edge
  have hcoledge (x : {x // x ∈ labels}) : (colSlot x).2 = edge.2 ∧ (cols.get (colSlot x).1).1 edge.2 = p edge.1 edge.2 := by
    exact fw_joint_actual_grid_pair_graph bc sc wc gc hc hsc hwc hgc p
      (bridgeStageLayer_endpoints bc hc p hcmap) (bridgeStageLayer_endpoints sc hsc p hscmap)
      (fun j k e => (hwideends j k e).2) (bridgeStageLayer_endpoints gc hgc p hgcmap) x edge
  exact fw_joint_row_column_grid_transport b rows cols p edge base rowGap colGap wide R
    hrowgrid hcolgrid rowSlot colSlot hrowinj hcolinj hrowgap hcolgap hrowedge hcoledge

end
end Sude
