import Sude.FWBridgeWideNetworkMatching
import Sude.DoubleBlockTranspose

/-! Exact wide-family contributions to physical row and column midpoints. All
unmatched orientations, non-wide cells and network deltas remain explicit. -/
namespace Sude
noncomputable section

/-- Instantiate the one-family partition with the actual wide band of the
joint row network. The grouped cells, decoder, supported blocks, and side
matches all refer to the same supplied geometry and new square. -/
theorem fw_wide_row_midpoint_partition {n L P : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr wc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hsr : sr.length = 16 * 3) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3)
    (hcells : Function.Injective (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc))
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
    let cells := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let T := fwWideJointPairImage br sr wr gr hwr
    let ι := fwWideJointToGrouped (fw_wide_stage_count_pos_of_geometry hwide hs) br sr wr gr hwr 0
    let A := Finset.univ.image cells
    let row := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
    let U := Finset.univ.biUnion network.block
    let line := fun c : Cell n => c.1 = r
    let gap := fun i => (entry new (cells (i,true)) : ℝ) - entry new (cells (i,false))
    (physicalNetworkMidpointTwice v network r : ℝ) =
      2 * doubleBlockActualCenteredScore cells line old new +
      2 * (∑ j, ∑ b, doubleBlockLineWeight cells line j b * doubleStageMidpointMean cells old j) +
      (∑ i ∈ Finset.univ \ T.image ι, gap i * physicalPairLineOrientation cells line i) +
      2 * (∑ c ∈ row \ A, (entry new c : ℝ)) +
      ∑ k ∈ U \ T, (rowNetworkDelta v k r : ℝ) := by
  classical
  exact double_block_physical_midpoint_partition
    (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) hcells old new v network
    (fwWideJointPairImage br sr wr gr hwr)
    (fw_wide_joint_image_subset_blocks br sr wr gr hbr hsr hwr hgr network.block hblock)
    (fwWideJointToGrouped (fw_wide_stage_count_pos_of_geometry hwide hs) br sr wr gr hwr 0)
    (fw_wide_joint_grouped_injective_on_image (fw_wide_stage_count_pos_of_geometry hwide hs) br sr wr gr hwr 0) r
    (fw_wide_joint_row_side_matching hwide hs choice (fw_wide_stage_count_pos_of_geometry hwide hs) br sr wr gr wc hwr hwc v hslot)


/-- Instantiate the grouped partition on the transposed joint column network,
then express its physical terms on the original square. -/
theorem fw_wide_column_midpoint_partition {n L P : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (wr bc sc wc gc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hbc : bc.length = 5 * 3)
    (hsc : sc.length = 16 * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgc : gc.length = P * 3)
    (hcells : Function.Injective (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc))
    (old new : Cell n ≃ Fin (n*n))
    (v : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n)
      (LayerPacking.transposePlacement new))
    (network : CenteredNetwork (Fin 3 × Fin n)
      (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) v)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) =
      layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (hblock : ∀ edge, network.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2)))
    (c : Fin n) :
    let cells := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let T := fwWideJointPairImage bc sc wc gc hwc
    let ι := fwWideJointToGrouped (fw_wide_stage_count_pos_of_geometry hwide hs) bc sc wc gc hwc 1
    let A := Finset.univ.image cells
    let col := (Finset.univ : Finset (Fin n)).image (fun r => (r,c))
    let U := Finset.univ.biUnion network.block
    let line := fun z : Cell n => z.2 = c
    let gap := fun i => (entry new (cells (i,true)) : ℝ) - entry new (cells (i,false))
    (physicalNetworkMidpointTwice v network c : ℝ) =
      2 * doubleBlockActualCenteredScore cells line old new +
      2 * (∑ j, ∑ b, doubleBlockLineWeight cells line j b * doubleStageMidpointMean cells old j) +
      (∑ i ∈ Finset.univ \ T.image ι, gap i * physicalPairLineOrientation cells line i) +
      2 * (∑ z ∈ col \ A, (entry new z : ℝ)) +
      ∑ k ∈ U \ T, (rowNetworkDelta v k c : ℝ) := by
  classical
  let cells := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
  have hcellst : Function.Injective (fun x => (cells x).swap) := by
    intro x y h
    apply hcells
    simpa using congrArg Prod.swap h
  have h := double_block_physical_midpoint_partition
    (fun x => (cells x).swap) hcellst (LayerPacking.transposePlacement old)
    (LayerPacking.transposePlacement new) v network
    (fwWideJointPairImage bc sc wc gc hwc)
    (fw_wide_joint_image_subset_blocks bc sc wc gc hbc hsc hwc hgc network.block hblock)
    (fwWideJointToGrouped (fw_wide_stage_count_pos_of_geometry hwide hs) bc sc wc gc hwc 1)
    (fw_wide_joint_grouped_injective_on_image (fw_wide_stage_count_pos_of_geometry hwide hs) bc sc wc gc hwc 1) c
    (fw_wide_joint_column_side_matching hwide hs choice (fw_wide_stage_count_pos_of_geometry hwide hs) wr bc sc wc gc hwr hwc v hslot)
  have hscore : doubleBlockActualCenteredScore (fun x => (cells x).swap)
      (fun z => z.1 = c) (LayerPacking.transposePlacement old) (LayerPacking.transposePlacement new) =
      doubleBlockActualCenteredScore cells (fun z => z.2 = c) old new := by
    exact double_block_actual_centered_score_transpose cells (fun z => z.2 = c) old new
  have hweight (j : Fin (3 * (n / 450))) (b : Fin (3 * (n + 8))) :
      doubleBlockLineWeight (fun x => (cells x).swap) (fun z => z.1 = c) j b =
      doubleBlockLineWeight cells (fun z => z.2 = c) j b := by
    exact double_block_line_weight_transpose cells (fun z => z.2 = c) j b
  have horientation (i : Fin (3 * (n / 450)) × Fin (3 * (n + 8)) × Fin 2) :
      physicalPairLineOrientation (fun x => (cells x).swap) (fun z => z.1 = c) i =
      physicalPairLineOrientation cells (fun z => z.2 = c) i := by
    exact physical_pair_line_orientation_transpose cells (fun z => z.2 = c) i
  dsimp only at h ⊢
  simpa only [hscore, hweight, double_stage_midpoint_mean_transpose, physical_pair_gap_transpose,
    horientation, physical_column_complement_transpose] using h

end
end Sude
