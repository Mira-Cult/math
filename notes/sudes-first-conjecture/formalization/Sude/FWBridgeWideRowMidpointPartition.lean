import Sude.DoubleBlockTwoFamilyMidpointPartition
import Sude.FWGroupedBridgeWideGeometry
import Sude.FWBridgeWideNetworkMatching

/-! A single exact physical-row midpoint partition for the actual bridge and
wide families, with all unmatched terms retained. -/
namespace Sude
noncomputable section

/-- Under the supplied joint packing and exact network maps, the two grouped
families contribute to one physical-row midpoint without duplicating the
complement or the unmatched network corrections. -/
theorem fw_bridge_wide_row_midpoint_partition {n P : ℕ}
    (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (old new : Cell n ≃ Fin (n*n))
    (v : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) new)
    (network : CenteredNetwork (Fin 3 × Fin n)
      (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) v)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) =
      layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hblock : ∀ edge, network.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (r : Fin n) :
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let Tb := fwBridgeJointPairImage br sr wr gr hbr
    let Tw := fwWideJointPairImage br sr wr gr hwr
    let ib := fwBridgeJointToGrouped br sr wr gr hbr 0
    let iw := fwWideJointToGrouped (fw_wide_stage_count_pos_of_geometry hwide hs) br sr wr gr hwr 0
    let Ab := Finset.univ.image bridge
    let Aw := Finset.univ.image wide
    let row := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
    let U := Finset.univ.biUnion network.block
    let line := fun c : Cell n => c.1 = r
    let gapb := fun i => (entry new (bridge (i,true)) : ℝ) - entry new (bridge (i,false))
    let gapw := fun i => (entry new (wide (i,true)) : ℝ) - entry new (wide (i,false))
    (physicalNetworkMidpointTwice v network r : ℝ) =
      (2 * doubleBlockActualCenteredScore bridge line old new +
        2 * (∑ j, ∑ b, doubleBlockLineWeight bridge line j b * doubleStageMidpointMean bridge old j) +
        ∑ i ∈ Finset.univ \ Tb.image ib, gapb i * physicalPairLineOrientation bridge line i) +
      (2 * doubleBlockActualCenteredScore wide line old new +
        2 * (∑ j, ∑ b, doubleBlockLineWeight wide line j b * doubleStageMidpointMean wide old j) +
        ∑ i ∈ Finset.univ \ Tw.image iw, gapw i * physicalPairLineOrientation wide line i) +
      2 * (∑ c ∈ row \ (Ab ∪ Aw), (entry new c : ℝ)) +
      ∑ k ∈ U \ (Tb ∪ Tw), (rowNetworkDelta v k r : ℝ) := by
  classical
  obtain ⟨hb, hw, hbw⟩ := fw_grouped_bridge_wide_geometry hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  exact double_block_two_family_midpoint_partition
    (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
    (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) hb hw hbw old new v network
    (fwBridgeJointPairImage br sr wr gr hbr) (fwWideJointPairImage br sr wr gr hwr)
    (fw_bridge_joint_image_subset_blocks br sr wr gr hbr hsr hwr hgr network.block hblock)
    (fw_wide_joint_image_subset_blocks br sr wr gr hbr hsr hwr hgr network.block hblock)
    (fw_bridge_wide_joint_images_disjoint br sr wr gr hbr hwr)
    (fwBridgeJointToGrouped br sr wr gr hbr 0)
    (fwWideJointToGrouped (fw_wide_stage_count_pos_of_geometry hwide hs) br sr wr gr hwr 0)
    (fw_bridge_joint_grouped_injective_on_image br sr wr gr hbr 0)
    (fw_wide_joint_grouped_injective_on_image (fw_wide_stage_count_pos_of_geometry hwide hs) br sr wr gr hwr 0) r
    (fw_bridge_joint_row_side_matching hrect hs choice br sr wr gr bc hbr hbc v hslot)
    (fw_wide_joint_row_side_matching hwide hs choice (fw_wide_stage_count_pos_of_geometry hwide hs) br sr wr gr wc hwr hwc v hslot)

end
end Sude
