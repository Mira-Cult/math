import Sude.FWBridgeWideNetworkMatching
import Sude.DoubleBlockTranspose

/-! Exact bridge-family contribution to a physical column midpoint. All
unmatched orientations, non-bridge cells and network deltas remain explicit. -/
namespace Sude
noncomputable section

/-- Instantiate the grouped partition on the transposed joint column network,
then express its physical terms on the original square. -/
theorem fw_bridge_column_midpoint_partition {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sc wc gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsc : sc.length = 16 * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgc : gc.length = P * 3)
    (hcells : Function.Injective (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc))
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
    let cells := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let T := fwBridgeJointPairImage bc sc wc gc hbc
    let ι := fwBridgeJointToGrouped bc sc wc gc hbc 1
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
  let cells := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
  have hcellst : Function.Injective (fun x => (cells x).swap) := by
    intro x y h
    apply hcells
    simpa using congrArg Prod.swap h
  have h := double_block_physical_midpoint_partition
    (fun x => (cells x).swap) hcellst (LayerPacking.transposePlacement old)
    (LayerPacking.transposePlacement new) v network
    (fwBridgeJointPairImage bc sc wc gc hbc)
    (fw_bridge_joint_image_subset_blocks bc sc wc gc hbc hsc hwc hgc network.block hblock)
    (fwBridgeJointToGrouped bc sc wc gc hbc 1)
    (fw_bridge_joint_grouped_injective_on_image bc sc wc gc hbc 1) c
    (fw_bridge_joint_column_side_matching hrect hs choice br bc sc wc gc hbr hbc v hslot)
  have hscore : doubleBlockActualCenteredScore (fun x => (cells x).swap)
      (fun z => z.1 = c) (LayerPacking.transposePlacement old) (LayerPacking.transposePlacement new) =
      doubleBlockActualCenteredScore cells (fun z => z.2 = c) old new := by
    exact double_block_actual_centered_score_transpose cells (fun z => z.2 = c) old new
  have hweight (j : Fin 5) (b : Fin (3 * (n + 8))) :
      doubleBlockLineWeight (fun x => (cells x).swap) (fun z => z.1 = c) j b =
      doubleBlockLineWeight cells (fun z => z.2 = c) j b := by
    exact double_block_line_weight_transpose cells (fun z => z.2 = c) j b
  have horientation (i : Fin 5 × Fin (3 * (n + 8)) × Fin 2) :
      physicalPairLineOrientation (fun x => (cells x).swap) (fun z => z.1 = c) i =
      physicalPairLineOrientation cells (fun z => z.2 = c) i := by
    exact physical_pair_line_orientation_transpose cells (fun z => z.2 = c) i
  dsimp only at h ⊢
  simpa only [hscore, hweight, double_stage_midpoint_mean_transpose, physical_pair_gap_transpose,
    horientation, physical_column_complement_transpose] using h

end
end Sude
