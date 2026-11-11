import Sude.FWJointSupportedGap
import Sude.FWPermutedJointEdgeGaps
import Sude.FWPermutedBridgeWideGrid

/-! Supported joint gap identities after stage-dependent bridge/wide
reallocation, on one supplied square. No grid or flow is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

theorem fw_permuted_joint_supported_gap {n L : ℕ}
    (reserved : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n reserved batches j)
    (hrect : 5 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    {stages : List BTSelectedStage} (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (new : Cell n ≃ Fin (n*n))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (hbgap : ∀ j b p, entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,p),true)) =
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,p),false)) +
        ((fwBridgeStageBlock n reserved batches hvalid j (πb j b)).high₁ -
          (fwBridgeStageBlock n reserved batches hvalid j (πb j b)).low₁))
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (hwgap : ∀ j b p, entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),true)) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),false)) +
        fwPermutedWideSourceGap blocks hlen πw j b)
    (edge : Fin 3 × Fin n) :
    let labels := fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))
    let index : Fin (3 * (n + 8)) := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge
    let rowGap := fwStageVaryingJoinedBridgeGap (fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge false)
      (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge false)) batches (fwPermutedBridgeIndex πb index)
    let colGap := fwStageVaryingJoinedBridgeGap (fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge true)
      (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge true)) batches (fwPermutedBridgeIndex πb index)
    let wide := fun j => fwPermutedWideSourceGap blocks hlen πw j index
    (∀ x : {x // x ∈ labels},
      fwPhysicalRowLayerGap new (((br ++ sr) ++ wr) ++ gr)
        (fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)).1 edge.2 =
          Sum.elim rowGap wide x.1) ∧
    (∀ x : {x // x ∈ labels},
      fwPhysicalColumnLayerGap new (((bc ++ sc) ++ wc) ++ gc)
        (fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)).1 edge.2 =
          Sum.elim colGap wide x.1) := by
  dsimp only
  constructor <;> rintro ⟨(((j | j) | j) | j), hj⟩
  all_goals simp only [fwJointActualGridPairIndex, fwJointGridPairIndex,
    fwJointSupportedPairIndex, fwJointSupportedLayerIndex, fwJointSupportedTagOfGrid,
    fwBridgeSupportStage, fwStageVaryingJoinedBridgeGap, Sum.elim_inl, Sum.elim_inr]
  · exact fw_seed_joint_row_gap new br sr wr gr sc hsr hsc _ j edge.1 edge.2
  · exact fw_growth_joint_row_grid_gap new offset hoff hs choice br sr wr gr gc hgr hgc _ j edge.1 edge.2
  · have hj' : j ∈ Finset.range 5 := fwJointGridLabels_supported _ hj
    have h := (fw_permuted_bridge_joint_edge_gap hrect hs choice br bc sr sc wr wc gr gc hr hc
      reserved batches hvalid new πb hbgap ⟨j, Finset.mem_range.mp hj'⟩ edge.1 edge.2).1
    simpa [fwPermutedBridgeIndex, Finset.mem_range.mp hj'] using h
  · have hp := fw_permuted_wide_ordinary_edge_gap hwide hs choice wr wc hwr hwc blocks hlen new πw
      (by simpa only [fwPermutedWideSourceGap] using hwgap) j edge
    exact (fw_wide_joint_selected_gap hwide hs choice br sr wr gr bc sc wc gc hwr hwc new
      j edge.1 edge.2 _ hp).1
  · exact fw_seed_joint_column_gap new sr bc sc wc gc hsr hsc _ j edge.1 edge.2
  · exact fw_growth_joint_column_grid_gap new offset hoff hs choice gr bc sc wc gc hgr hgc _ j edge.1 edge.2
  · have hj' : j ∈ Finset.range 5 := fwJointGridLabels_supported _ hj
    have h := (fw_permuted_bridge_joint_edge_gap hrect hs choice br bc sr sc wr wc gr gc hr hc
      reserved batches hvalid new πb hbgap ⟨j, Finset.mem_range.mp hj'⟩ edge.1 edge.2).2.1
    simpa [fwPermutedBridgeIndex, Finset.mem_range.mp hj'] using h
  · have hp := fw_permuted_wide_ordinary_edge_gap hwide hs choice wr wc hwr hwc blocks hlen new πw
      (by simpa only [fwPermutedWideSourceGap] using hwgap) j edge
    exact (fw_wide_joint_selected_gap hwide hs choice br sr wr gr bc sc wc gc hwr hwc new
      j edge.1 edge.2 _ hp).2

/-- The supplied seed/growth grids on both networks extend to complete grids
on actual joint-layer slots of the same reallocated square. The radius is
recomputed from the stage-permuted bridge and wide source gaps. -/
theorem fw_permuted_joint_physical_grids {n L : ℕ}
    (reserved : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n reserved batches j)
    (hrect : 5 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    {stages : List BTSelectedStage} (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (new : Cell n ≃ Fin (n*n))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (hbgap : ∀ j b p, entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,p),true)) =
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,p),false)) +
        ((fwBridgeStageBlock n reserved batches hvalid j (πb j b)).high₁ -
          (fwBridgeStageBlock n reserved batches hvalid j (πb j b)).low₁))
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (hwgap : ∀ j b p, entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),true)) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),false)) +
        fwPermutedWideSourceGap blocks hlen πw j b)
    (edge : Fin 3 × Fin n) (radius : ℕ)
    (hinitial : ∀ network : Bool,
      CompleteEvenGrid (Finset.univ : Finset (Fin 16 ⊕ Fin stages.length))
        (fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge network)
          (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network)) radius)
    (heven : 2 ∣ radius) (hcross : (poolMaximum n : ℝ) / 23 ≤ radius)
    (μ : ℝ) (hX : (100 : ℝ) ≤ poolMaximum n)
    (hmlo : (243 / 500 : ℝ) * poolMaximum n ≤ μ)
    (hmhi : μ ≤ (123 / 250 : ℝ) * poolMaximum n)
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n)))) :
    let index : Fin (3 * (n + 8)) := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge
    let R := radius + (∑ j ∈ Finset.range 5, selectedBridgeGap batches (fwPermutedBridgeIndex πb index j) j) +
      ∑ j, fwPermutedWideSourceGap blocks hlen πw j index
    let labels := fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))
    let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
    let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
    CompleteEvenGrid (labels.attach.image rowSlot) (fun x => fwPhysicalRowLayerGap new (((br ++ sr) ++ wr) ++ gr) x.1 x.2) R ∧
    CompleteEvenGrid (labels.attach.image colSlot) (fun x => fwPhysicalColumnLayerGap new (((bc ++ sc) ++ wc) ++ gc) x.1 x.2) R ∧
    2 ∣ R := by
  classical
  dsimp only
  let index : Fin (3 * (n + 8)) := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge
  let labels := fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))
  let R := radius + (∑ j ∈ Finset.range 5, selectedBridgeGap batches (fwPermutedBridgeIndex πb index j) j) +
      ∑ j, fwPermutedWideSourceGap blocks hlen πw j index
  let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
  let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
  let rowGap := fwStageVaryingJoinedBridgeGap (fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge false)
    (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge false)) batches (fwPermutedBridgeIndex πb index)
  let colGap := fwStageVaryingJoinedBridgeGap (fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge true)
    (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge true)) batches (fwPermutedBridgeIndex πb index)
  let wide := fun j => fwPermutedWideSourceGap blocks hlen πw j index
  have hg (network : Bool) := fw_permuted_bridge_wide_source_grid reserved batches hvalid πb πw index
    (Finset.univ : Finset (Fin 16 ⊕ Fin stages.length))
    (fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge network)
      (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network)) radius
    (hinitial network) heven hcross μ hX hmlo hmhi blocks hlen hmatched
  have hrgrid : CompleteEvenGrid labels (Sum.elim rowGap wide) R := by
    simpa only [labels, fwJointGridLabels, fwJointPreWideGridLabels, R, index, rowGap, wide] using (hg false).2.2.2.2.1
  have hcgrid : CompleteEvenGrid labels (Sum.elim colGap wide) R := by
    simpa only [labels, fwJointGridLabels, fwJointPreWideGridLabels, R, index, colGap, wide] using (hg true).2.2.2.2.1
  have hR : 2 ∣ R := by simpa only [R, index, wide] using (hg false).2.2.2.2.2.1
  have hrowinj : Function.Injective rowSlot := by
    intro x y heq
    have h := fwJointActualGridPairIndex_injective br sr wr gr hr hsr hwr hgr heq
    exact congrArg (fun z => z.1.1) h
  have hcolinj : Function.Injective colSlot := by
    intro x y heq
    have h := fwJointActualGridPairIndex_injective bc sc wc gc hc hsc hwc hgc heq
    exact congrArg (fun z => z.1.1) h
  obtain ⟨hrgap, hcgap⟩ := fw_permuted_joint_supported_gap reserved batches hvalid hrect hwide hs choice
    br bc hr hc sr sc hsr hsc wr wc hwr hwc offset hoff gr gc hgr hgc new πb hbgap blocks hlen πw hwgap edge
  refine ⟨?_, ?_, hR⟩
  · apply completeEvenGrid_finite_relabel labels (Sum.elim rowGap wide) R rowSlot hrowinj
      (fun x => fwPhysicalRowLayerGap new (((br ++ sr) ++ wr) ++ gr) x.1 x.2) ?_ hrgrid
    intro x
    exact hrgap x
  · apply completeEvenGrid_finite_relabel labels (Sum.elim colGap wide) R colSlot hcolinj
      (fun x => fwPhysicalColumnLayerGap new (((bc ++ sc) ++ wc) ++ gc) x.1 x.2) ?_ hcgrid
    intro x
    exact hcgap x

end
end Sude
