import Sude.FWBridgeWideColumnMidpointPartition
import Sude.FWBridgeWideUnmatchedColumnOrientation
import Sude.FWTraceResidualCancellation

/-! Exact same-square bridge/wide column midpoint identity after cancellation
of unmatched orientations and the trace-preserved network residual. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- The reference `base`, trace placement `grown`, and final square `new`
are kept separate. Both pairs of each bridge or wide rectangle must have equal
gaps on `new`; different rectangles can have different gaps. -/
theorem fw_trace_bridge_wide_column_midpoint {g Q n : ℕ}
    {initial final : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ Q) (hdiag : (4 * 6) * 2 ≤ Q)
    (hP : stages.length ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hfull : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + stages.length * (4 * 6) ≤ fwJointRectangleCount n 254)
    (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (base grown new : Cell n ≃ Fin (n*n))
    (hplaced : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
        (trace.poolValues rfl hpool (prefixPhysicalInput hfit hdiag x)).val)
    (hfixed : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
        entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x))
    (hseedgap : ∀ j q, entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),true)) =
       entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),false)) + 2)
    (vr : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) new)
    (vc : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (LayerPacking.transposePlacement new))
    (network : CenteredNetwork (Fin 3 × Fin n) (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) vc)
    (hslotr : ∀ t side, rowNetworkSlot vr (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hslotc : ∀ t side, rowNetworkSlot vc (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (blocksR : (Fin 3 × Fin n) → Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n))
    (hblockr : ∀ edge, blocksR edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (hblockc : ∀ edge, network.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2)))
    (hgapb : ∀ j (rect : Fin (4 * 6)),
      let cells := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
      ((entry new (cells ((j, Fin.castLE (by omega) rect, 0),true)) : ℝ) - entry new (cells ((j, Fin.castLE (by omega) rect, 0),false))) =
      ((entry new (cells ((j, Fin.castLE (by omega) rect, 1),true)) : ℝ) - entry new (cells ((j, Fin.castLE (by omega) rect, 1),false))))
    (hgapw : ∀ j (rect : Fin (4 * 6)),
      let cells := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
      ((entry new (cells ((j, Fin.castLE (by omega) rect, 0),true)) : ℝ) - entry new (cells ((j, Fin.castLE (by omega) rect, 0),false))) =
      ((entry new (cells ((j, Fin.castLE (by omega) rect, 1),true)) : ℝ) - entry new (cells ((j, Fin.castLE (by omega) rect, 1),false))))
    (c : Fin n) :
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let col := (Finset.univ : Finset (Fin n)).image (fun r => (r,c))
    let line := fun z : Cell n => z.2 = c
    (physicalNetworkMidpointTwice vc network c : ℝ) =
      (2 * doubleBlockActualCenteredScore bridge line base new +
        2 * (∑ j, ∑ b, doubleBlockLineWeight bridge line j b * doubleStageMidpointMean bridge base j)) +
      (2 * doubleBlockActualCenteredScore wide line base new +
        2 * (∑ j, ∑ b, doubleBlockLineWeight wide line j b * doubleStageMidpointMean wide base j)) +
      2 * (∑ z ∈ col \ (Finset.univ.image bridge ∪ Finset.univ.image wide), (entry new z : ℝ)) := by
  classical
  let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
  let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
  let gapb := fun i => (entry new (bridge (i,true)) : ℝ) - entry new (bridge (i,false))
  let gapw := fun i => (entry new (wide (i,true)) : ℝ) - entry new (wide (i,false))
  have hb := fw_bridge_unmatched_column_orientation_zero hrect hs choice br bc sc wc gc hbr hbc gapb hgapb c
  have hw := fw_wide_unmatched_column_orientation_zero hwide hs choice wr bc sc wc gc hwr hwc
    (fw_wide_stage_count_pos_of_geometry hwide hs) gapw hgapw c
  have hc := (fw_trace_seed_growth_residual_cancellation trace hpool hfit hdiag offset hoff hseed hs choice
    br sr wr gr bc sc wc gc hbr hsr hwr hgr hbc hsc hwc hgc grown new hplaced hfixed hseedgap vr vc hslotr hslotc
    blocksR network.block hblockr hblockc c c).2
  have h := fw_bridge_wide_column_midpoint_partition hP hrect hseed hwide hfull hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols base new vc network hslotc hblockc c
  dsimp only at h ⊢
  rw [hb, hw, hc] at h
  simpa using h

end
end Sude
