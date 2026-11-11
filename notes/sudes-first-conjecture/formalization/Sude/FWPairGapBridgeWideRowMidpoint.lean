import Sude.FWBridgeWideRowMidpointPartition
import Sude.FWBridgeWideUnmatchedRowOrientation
import Sude.FWPairGapResidualCancellation

/-! Exact actual bridge/wide row midpoint identity after cancellation of
unmatched orientations and the same-square seed/growth network residual.
The physical complement remains explicit. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- For a supplied common new square, packing, side-matched networks, seed
endpoints and stagewise growth pair gaps, the remaining row midpoint
contains both bridge/wide centered scores, their original-source means, and
one physical-cell complement. This is not a complete-line bound. -/
theorem fw_pair_gap_bridge_wide_row_midpoint
    {n : ℕ} {stages : List BTSelectedStage}
    (hP : stages.length ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + stages.length * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (source new : Cell n ≃ Fin (n*n))
    (hpairgap : ∀ j i, entry new (btGrowingOffsetPairCells
      (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc ((j,i),true)) =
      entry new (btGrowingOffsetPairCells
        (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc ((j,i),false)) + (stages.get j).gap)
    (hseedgap : ∀ j q, entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),true)) =
       entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),false)) + 2)
    (vr : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) new)
    (vc : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (LayerPacking.transposePlacement new))
    (networkR : CenteredNetwork (Fin 3 × Fin n) (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) vr)
    (blocksC : (Fin 3 × Fin n) → Finset (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n))
    (hslotr : ∀ t side, rowNetworkSlot vr (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hslotc : ∀ t side, rowNetworkSlot vc (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (hblockr : ∀ edge, networkR.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (hblockc : ∀ edge, blocksC edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2)))
    (r : Fin n) :
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let Ab := Finset.univ.image bridge
    let Aw := Finset.univ.image wide
    let row := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
    let line := fun c : Cell n => c.1 = r
    (physicalNetworkMidpointTwice vr networkR r : ℝ) =
      (2 * doubleBlockActualCenteredScore bridge line source new +
        2 * (∑ j, ∑ b, doubleBlockLineWeight bridge line j b * doubleStageMidpointMean bridge source j)) +
      (2 * doubleBlockActualCenteredScore wide line source new +
        2 * (∑ j, ∑ b, doubleBlockLineWeight wide line j b * doubleStageMidpointMean wide source j)) +
      2 * (∑ c ∈ row \ (Ab ∪ Aw), (entry new c : ℝ)) := by
  classical
  have hp := fw_bridge_wide_row_midpoint_partition hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols source new vr networkR hslotr hblockr r
  have hb := fw_bridge_unmatched_row_orientation_zero hrect hs choice br bc sr wr gr hbr hbc
    (fun i => (entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc (i,true)) : ℝ) -
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc (i,false))) r
  have hw := fw_wide_unmatched_row_orientation_zero hwide hs choice br sr wr gr wc hwr hwc
    (fw_wide_stage_count_pos_of_geometry hwide hs)
    (fun i => (entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc (i,true)) : ℝ) -
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc (i,false))) r
  have hz := (fw_pair_gap_seed_growth_residual_cancellation
    (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hseed hs choice
    br sr wr gr bc sc wc gc hbr hsr hwr hgr hbc hsc hwc hgc new hpairgap hseedgap
    vr vc hslotr hslotc networkR.block blocksC hblockr hblockc r r).1
  dsimp only at hp ⊢
  rw [hb, hw, hz] at hp
  simpa using hp

end
end Sude
