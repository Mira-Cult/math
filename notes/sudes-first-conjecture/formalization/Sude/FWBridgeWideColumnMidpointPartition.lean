import Sude.DoubleBlockTwoFamilyMidpointPartition
import Sude.FWGroupedBridgeWideGeometry
import Sude.FWBridgeWideNetworkMatching
import Sude.DoubleBlockTranspose

/-! A single exact physical-column midpoint partition for the actual bridge and
wide families, with all unmatched terms retained. -/
namespace Sude
noncomputable section

/-- Transposition carries the complement of two physical families to the
corresponding complement of their transposed images. -/
theorem physical_column_two_family_complement_transpose {n : ℕ} {α β : Type*}
    [Fintype α] [Fintype β] (cells₁ : α → Cell n) (cells₂ : β → Cell n)
    (a : Cell n ≃ Fin (n*n)) (c : Fin n) :
    (∑ z ∈ ((Finset.univ : Finset (Fin n)).image (fun r => (c,r))) \
        (Finset.univ.image (fun x => (cells₁ x).swap) ∪
          Finset.univ.image (fun x => (cells₂ x).swap)),
      (entry (LayerPacking.transposePlacement a) z : ℝ)) =
    ∑ z ∈ ((Finset.univ : Finset (Fin n)).image (fun r => (r,c))) \
        (Finset.univ.image cells₁ ∪ Finset.univ.image cells₂), (entry a z : ℝ) := by
  classical
  have hswap : Function.Injective (Prod.swap : Cell n → Cell n) := by
    intro x y h
    simpa using congrArg Prod.swap h
  have hsets :
      ((Finset.univ : Finset (Fin n)).image (fun r => (c,r)) \
        (Finset.univ.image (fun x => (cells₁ x).swap) ∪
          Finset.univ.image (fun x => (cells₂ x).swap))) =
      (((Finset.univ : Finset (Fin n)).image (fun r => (r,c)) \
        (Finset.univ.image cells₁ ∪ Finset.univ.image cells₂)).image Prod.swap) := by
    rw [Finset.image_sdiff _ _ hswap, Finset.image_union]
    simp only [Finset.image_image, Function.comp_def, Prod.swap_prod_mk]
  rw [hsets, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro z _
    cases z
    rfl
  · intro x _ y _ h
    exact hswap h

/-- Under the supplied joint packing and exact network maps, the two grouped
families contribute to one physical-column midpoint without duplicating the
complement or the unmatched network corrections. -/
theorem fw_bridge_wide_column_midpoint_partition {n P : ℕ}
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
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let Tb := fwBridgeJointPairImage bc sc wc gc hbc
    let Tw := fwWideJointPairImage bc sc wc gc hwc
    let ib := fwBridgeJointToGrouped bc sc wc gc hbc 1
    let iw := fwWideJointToGrouped (fw_wide_stage_count_pos_of_geometry hwide hs) bc sc wc gc hwc 1
    let Ab := Finset.univ.image bridge
    let Aw := Finset.univ.image wide
    let col := (Finset.univ : Finset (Fin n)).image (fun r => (r,c))
    let U := Finset.univ.biUnion network.block
    let line := fun z : Cell n => z.2 = c
    let gapb := fun i => (entry new (bridge (i,true)) : ℝ) - entry new (bridge (i,false))
    let gapw := fun i => (entry new (wide (i,true)) : ℝ) - entry new (wide (i,false))
    (physicalNetworkMidpointTwice v network c : ℝ) =
      (2 * doubleBlockActualCenteredScore bridge line old new +
        2 * (∑ j, ∑ b, doubleBlockLineWeight bridge line j b * doubleStageMidpointMean bridge old j) +
        ∑ i ∈ Finset.univ \ Tb.image ib, gapb i * physicalPairLineOrientation bridge line i) +
      (2 * doubleBlockActualCenteredScore wide line old new +
        2 * (∑ j, ∑ b, doubleBlockLineWeight wide line j b * doubleStageMidpointMean wide old j) +
        ∑ i ∈ Finset.univ \ Tw.image iw, gapw i * physicalPairLineOrientation wide line i) +
      2 * (∑ z ∈ col \ (Ab ∪ Aw), (entry new z : ℝ)) +
      ∑ k ∈ U \ (Tb ∪ Tw), (rowNetworkDelta v k c : ℝ) := by
  classical
  let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
  let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
  obtain ⟨hb, hw, hbw⟩ := fw_grouped_bridge_wide_geometry hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  have hbt : Function.Injective (fun x => (bridge x).swap) := by
    intro x y h
    apply hb
    simpa using congrArg Prod.swap h
  have hwt : Function.Injective (fun x => (wide x).swap) := by
    intro x y h
    apply hw
    simpa using congrArg Prod.swap h
  have hbwt : Disjoint (Finset.univ.image (fun x => (bridge x).swap))
      (Finset.univ.image (fun x => (wide x).swap)) := by
    apply Finset.disjoint_left.mpr
    intro z hz₁ hz₂
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz₁
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hz₂
    apply Finset.disjoint_left.mp hbw (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
    apply Finset.mem_image.mpr
    refine ⟨y, Finset.mem_univ _, ?_⟩
    simpa using congrArg Prod.swap (hy.trans hx.symm)
  have h := double_block_two_family_midpoint_partition
    (fun x => (bridge x).swap) (fun x => (wide x).swap) hbt hwt hbwt
    (LayerPacking.transposePlacement old) (LayerPacking.transposePlacement new) v network
    (fwBridgeJointPairImage bc sc wc gc hbc) (fwWideJointPairImage bc sc wc gc hwc)
    (fw_bridge_joint_image_subset_blocks bc sc wc gc hbc hsc hwc hgc network.block hblock)
    (fw_wide_joint_image_subset_blocks bc sc wc gc hbc hsc hwc hgc network.block hblock)
    (fw_bridge_wide_joint_images_disjoint bc sc wc gc hbc hwc)
    (fwBridgeJointToGrouped bc sc wc gc hbc 1)
    (fwWideJointToGrouped (fw_wide_stage_count_pos_of_geometry hwide hs) bc sc wc gc hwc 1)
    (fw_bridge_joint_grouped_injective_on_image bc sc wc gc hbc 1)
    (fw_wide_joint_grouped_injective_on_image (fw_wide_stage_count_pos_of_geometry hwide hs) bc sc wc gc hwc 1) c
    (fw_bridge_joint_column_side_matching hrect hs choice br bc sc wc gc hbr hbc v hslot)
    (fw_wide_joint_column_side_matching hwide hs choice (fw_wide_stage_count_pos_of_geometry hwide hs) wr bc sc wc gc hwr hwc v hslot)
  have hscoreb : doubleBlockActualCenteredScore (fun x => (bridge x).swap)
      (fun z => z.1 = c) (LayerPacking.transposePlacement old) (LayerPacking.transposePlacement new) =
      doubleBlockActualCenteredScore bridge (fun z => z.2 = c) old new := by
    exact double_block_actual_centered_score_transpose bridge (fun z => z.2 = c) old new
  have hscorew : doubleBlockActualCenteredScore (fun x => (wide x).swap)
      (fun z => z.1 = c) (LayerPacking.transposePlacement old) (LayerPacking.transposePlacement new) =
      doubleBlockActualCenteredScore wide (fun z => z.2 = c) old new := by
    exact double_block_actual_centered_score_transpose wide (fun z => z.2 = c) old new
  have hweightb (j : Fin 5) (b : Fin (3 * (n + 8))) :
      doubleBlockLineWeight (fun x => (bridge x).swap) (fun z => z.1 = c) j b =
      doubleBlockLineWeight bridge (fun z => z.2 = c) j b := by
    exact double_block_line_weight_transpose bridge (fun z => z.2 = c) j b
  have hweightw (j : Fin (3 * (n / 450))) (b : Fin (3 * (n + 8))) :
      doubleBlockLineWeight (fun x => (wide x).swap) (fun z => z.1 = c) j b =
      doubleBlockLineWeight wide (fun z => z.2 = c) j b := by
    exact double_block_line_weight_transpose wide (fun z => z.2 = c) j b
  have horientationb (i : Fin 5 × Fin (3 * (n + 8)) × Fin 2) :
      physicalPairLineOrientation (fun x => (bridge x).swap) (fun z => z.1 = c) i =
      physicalPairLineOrientation bridge (fun z => z.2 = c) i := by
    exact physical_pair_line_orientation_transpose bridge (fun z => z.2 = c) i
  have horientationw (i : Fin (3 * (n / 450)) × Fin (3 * (n + 8)) × Fin 2) :
      physicalPairLineOrientation (fun x => (wide x).swap) (fun z => z.1 = c) i =
      physicalPairLineOrientation wide (fun z => z.2 = c) i := by
    exact physical_pair_line_orientation_transpose wide (fun z => z.2 = c) i
  dsimp only at h ⊢
  simpa only [hscoreb, hscorew, hweightb, hweightw, double_stage_midpoint_mean_transpose,
    physical_pair_gap_transpose, horientationb, horientationw,
    physical_column_two_family_complement_transpose] using h

end
end Sude
