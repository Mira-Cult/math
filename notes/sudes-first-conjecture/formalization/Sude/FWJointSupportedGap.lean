import Sude.FWJointSupportedIndex

/-! Physical gap preservation for the supported seed/growth/bridge/wide
labels at one actual graph edge. No grid transport or flow is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- The joint pair index retains the selected physical gap on both networks.
The same supplied `wide` family is used on both sides. -/
theorem fw_joint_supported_gap_eq {n L : ℕ}
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
    {stages : List BTSelectedStage} (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (edge : Fin 3 × Fin n) (wide : Fin (3 * (n / 450)) → ℕ)
    (hwidepair : ∀ (j : Fin (3 * (n / 450))) (network : Bool),
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide j) :
    let labels := fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))
    let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
    let rowGap := joinedBridgeGap (fwPhysicalEdgeTraceGap grown (fwSeedEdgeCells sr sc hsr hsc edge false)
      (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge false)) batches index
    let colGap := joinedBridgeGap (fwPhysicalEdgeTraceGap grown (fwSeedEdgeCells sr sc hsr hsc edge true)
      (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge true)) batches index
    (∀ x : {x // x ∈ labels},
      fwPhysicalRowLayerGap grown (((br ++ sr) ++ wr) ++ gr)
        (fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)).1 edge.2 =
          Sum.elim rowGap wide x.1) ∧
    (∀ x : {x // x ∈ labels},
      fwPhysicalColumnLayerGap grown (((bc ++ sc) ++ wc) ++ gc)
        (fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)).1 edge.2 =
          Sum.elim colGap wide x.1) := by
  dsimp only
  constructor <;> rintro ⟨(((j | j) | j) | j), hj⟩
  all_goals simp only [fwJointActualGridPairIndex, fwJointGridPairIndex,
    fwJointSupportedPairIndex, fwJointSupportedLayerIndex, fwJointSupportedTagOfGrid,
    fwBridgeSupportStage, joinedBridgeGap, Sum.elim_inl, Sum.elim_inr]
  · exact fw_seed_joint_row_gap grown br sr wr gr sc hsr hsc _ j edge.1 edge.2
  · exact fw_growth_joint_row_grid_gap grown offset hoff hs choice br sr wr gr gc hgr hgc _ j edge.1 edge.2
  · have hj' : j ∈ Finset.range 5 := fwJointGridLabels_supported _ hj
    exact (fw_bridge_joint_selected_gap batches hvalid hrect hseed hwide hs choice br bc hr hc sr sc hsr hsc
      wr wc hwr hwc old grown hfixed hplace gr gc ⟨j, Finset.mem_range.mp hj'⟩ edge.1 edge.2).1
  · exact (fw_wide_joint_selected_gap hwide hs choice br sr wr gr bc sc wc gc hwr hwc grown
      j edge.1 edge.2 (wide j) (hwidepair j)).1
  · exact fw_seed_joint_column_gap grown sr bc sc wc gc hsr hsc _ j edge.1 edge.2
  · exact fw_growth_joint_column_grid_gap grown offset hoff hs choice gr bc sc wc gc hgr hgc _ j edge.1 edge.2
  · have hj' : j ∈ Finset.range 5 := fwJointGridLabels_supported _ hj
    exact (fw_bridge_joint_selected_gap batches hvalid hrect hseed hwide hs choice br bc hr hc sr sc hsr hsc
      wr wc hwr hwc old grown hfixed hplace gr gc ⟨j, Finset.mem_range.mp hj'⟩ edge.1 edge.2).2
  · exact (fw_wide_joint_selected_gap hwide hs choice br sr wr gr bc sc wc gc hwr hwc grown
      j edge.1 edge.2 (wide j) (hwidepair j)).2

end
end Sude
