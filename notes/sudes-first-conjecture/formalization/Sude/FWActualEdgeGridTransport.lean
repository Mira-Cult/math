import Sude.FWJointSupportedGap
import Sude.FWJointGraphEndpoints
import Sude.FWWideGapUniqueness

/-! Transport the supplied same-witness bridge/wide grids to actual joint
row and column pair indices. This does not assert cross-edge disjointness,
select a flow, or prove line repair. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- Reconcile the two wide-grid choices at one physical edge and transport
both grids to actual joint-layer slots of the same square and graph. -/
theorem fw_actual_edge_joint_grids {n L : ℕ}
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
    (hwc : wc.length = (3 * (n / 450)) * 3) (old grown : Cell n ≃ Fin (n*n))
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
    (last : ℕ) (edge : Fin 3 × Fin n)
    (hwidegrid : ∀ network : Bool,
      let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
      let radius := last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j
      let initialGap := fwPhysicalEdgeTraceGap grown (fwSeedEdgeCells sr sc hsr hsc edge network)
        (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network)
      let base := fwJointPreWideGridLabels stages.length
      ∃ wide : Fin (3 * (n / 450)) → ℕ,
        (∀ j, 0 < wide j ∧ 2 ∣ wide j ∧
          (∀ network : Bool,
            entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
            entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide j) ∧
          (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (wide j : ℝ) ∧ (wide j : ℝ) < poolMaximum n) ∧
        CompleteEvenGrid (fwJointGridLabels base (3 * (n / 450)))
          (Sum.elim (joinedBridgeGap initialGap batches index) wide) (radius + ∑ j, wide j) ∧
        2 ∣ radius + ∑ j, wide j ∧
        (2 : ℝ) * (n / 450 : ℕ) * (poolMaximum n : ℝ) ≤ ∑ j, (wide j : ℝ)) :
    let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
    let radius := last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j
    let labels := fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))
    let rows := ((br ++ sr) ++ wr) ++ gr
    let cols := ((bc ++ sc) ++ wc) ++ gc
    let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
    let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
    ∃ wide : Fin (3 * (n / 450)) → ℕ,
      (∀ j, 0 < wide j ∧ 2 ∣ wide j ∧
        (∀ network : Bool,
          entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
          entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide j) ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (wide j : ℝ) ∧ (wide j : ℝ) < poolMaximum n) ∧
      CompleteEvenGrid (labels.attach.image rowSlot) (fun x => fwPhysicalRowLayerGap grown rows x.1 x.2)
        (radius + ∑ j, wide j) ∧
      CompleteEvenGrid (labels.attach.image colSlot) (fun x => fwPhysicalColumnLayerGap grown cols x.1 x.2)
        (radius + ∑ j, wide j) ∧
      (∀ x side, LayerPacking.sequenceCell rows ((rowSlot x).1, ((rowSlot x).2, side)) =
        ((if side then p edge.1 edge.2 else edge.2), (rows.get (rowSlot x).1).2 edge.2)) ∧
      (∀ x side, (LayerPacking.sequenceCell cols ((colSlot x).1, ((colSlot x).2, side))).swap =
        ((cols.get (colSlot x).1).2 edge.2, (if side then p edge.1 edge.2 else edge.2))) ∧
      2 ∣ radius + ∑ j, wide j ∧
      (2 : ℝ) * (n / 450 : ℕ) * (poolMaximum n : ℝ) ≤ ∑ j, (wide j : ℝ) := by
  dsimp only
  let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
  let radius := last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j
  let base := fwJointPreWideGridLabels stages.length
  let rowGap := joinedBridgeGap (fwPhysicalEdgeTraceGap grown (fwSeedEdgeCells sr sc hsr hsc edge false)
    (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge false)) batches index
  let colGap := joinedBridgeGap (fwPhysicalEdgeTraceGap grown (fwSeedEdgeCells sr sc hsr hsc edge true)
    (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge true)) batches index
  obtain ⟨wide, hw, hrowgrid, hcolgrid, heven, hsum⟩ :=
    fw_reconcile_physical_wide_edge_grids (poolMaximum n) base rowGap colGap radius
      hwide hs choice wr wc hwr hwc grown edge.1 edge.2 (hwidegrid false) (hwidegrid true)
  let rows := ((br ++ sr) ++ wr) ++ gr
  let cols := ((bc ++ sc) ++ wc) ++ gc
  let labels := fwJointGridLabels base (3 * (n / 450))
  let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
  let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
  have hrowinj : Function.Injective rowSlot := by
    intro x y heq
    have h := fwJointActualGridPairIndex_injective br sr wr gr hr hsr hwr hgr heq
    exact congrArg (fun z => z.1.1) h
  have hcolinj : Function.Injective colSlot := by
    intro x y heq
    have h := fwJointActualGridPairIndex_injective bc sc wc gc hc hsc hwc hgc heq
    exact congrArg (fun z => z.1.1) h
  obtain ⟨hrowgap, hcolgap⟩ := fw_joint_supported_gap_eq batches hvalid hrect hseed hwide hs choice
    br bc hr hc sr sc hsr hsc wr wc hwr hwc old grown hfixed hplace offset hoff gr gc hgr hgc edge wide
    (fun j network => (hw j).2.2.1 network)
  have hwideends := fw_wide_layer_endpoints_of_physical_coordinates hwide hs choice wr wc hwr hwc p hwidecoords
  have hrowedge (x : {x // x ∈ labels}) : (rowSlot x).2 = edge.2 ∧ (rows.get (rowSlot x).1).1 edge.2 = p edge.1 edge.2 := by
    exact fw_joint_actual_grid_pair_graph br sr wr gr hr hsr hwr hgr p
      (bridgeStageLayer_endpoints br hr p hrmap) (bridgeStageLayer_endpoints sr hsr p hsrmap)
      (fun j k e => (hwideends j k e).1) (bridgeStageLayer_endpoints gr hgr p hgrmap) x edge
  have hcoledge (x : {x // x ∈ labels}) : (colSlot x).2 = edge.2 ∧ (cols.get (colSlot x).1).1 edge.2 = p edge.1 edge.2 := by
    exact fw_joint_actual_grid_pair_graph bc sc wc gc hc hsc hwc hgc p
      (bridgeStageLayer_endpoints bc hc p hcmap) (bridgeStageLayer_endpoints sc hsc p hscmap)
      (fun j k e => (hwideends j k e).2) (bridgeStageLayer_endpoints gc hgc p hgcmap) x edge
  have hresult := fw_joint_row_column_grid_transport grown rows cols p edge base rowGap colGap wide
    (radius + ∑ j, wide j) hrowgrid hcolgrid rowSlot colSlot hrowinj hcolinj hrowgap hcolgap hrowedge hcoledge
  exact ⟨wide, hw, hresult.1, hresult.2.1, hresult.2.2.1, hresult.2.2.2, heven, hsum⟩

end
end Sude
