import Sude.FWSeedNetworkMatching
import Sude.FWJointSupportedCellSeparation

/-! Exact physical overlap between the offset seed cells and a packed joint
ordinary network. The rectangle reservation and normalized two-network
packing are essential hypotheses. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- A packed row-network endpoint lies in the full offset seed-cell image
exactly when its pair index is in the seed band. -/
theorem fw_seed_row_network_slot_iff {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rect : Finset (Cell n))
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hrect : ∀ i side, packedRectangleCorner hs choice (i,side) ∈ rect)
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) a)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (t : Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) (side : Bool) :
    rowNetworkSlot v (t,side) ∈ Set.range (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) ↔
      t ∈ fwSeedJointPairImage br sr wr gr hsr := by
  classical
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  constructor
  · rintro ⟨⟨⟨j,q⟩, s⟩, heq⟩
    obtain ⟨tag, htag⟩ := (prefixStagePairSlot_bijective hfit hdiag hexact).2 q
    rw [← htag] at heq
    cases tag with
    | inl z =>
      rcases z with ⟨i, pair⟩
      simp only [prefixStagePairSlot] at heq
      rw [fw_seed_existing_rectangle_cell] at heq
      have hm := hrect (fwSeedRectangle hseed (finProdFinEquiv (j,i))) (prefixPairCorner pair s)
      have hn := hrows.sequenceCell_unreserved (t.1, (t.2, side))
      apply False.elim
      apply hn
      change layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side ∈ rect
      rw [← hslot, ← heq]
      exact hm
    | inr z =>
      rcases z with ⟨net, k, e⟩
      fin_cases net
      · simp only [prefixStagePairSlot] at heq
        change fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
          ((j, prefixOrdinaryPairIndex hfit ((0 : Fin 2), k, e)), s) = rowNetworkSlot v (t,side) at heq
        rw [fw_seed_existing_joint_row_match hseed hs choice br sr wr gr sc hsr hsc] at heq
        rw [← hslot] at heq
        have hp := rowNetworkSlot_injective v heq
        have ht := congrArg Prod.fst hp
        unfold fwSeedJointPairImage
        refine Finset.mem_image.mpr ⟨((j,k),e), Finset.mem_univ _, ?_⟩
        exact ht
      · simp only [prefixStagePairSlot] at heq
        change fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
          ((j, prefixOrdinaryPairIndex hfit ((1 : Fin 2), k, e)), s) = rowNetworkSlot v (t,side) at heq
        rw [fw_seed_existing_joint_column_match hseed hs choice sr bc sc wc gc hsr hsc] at heq
        rw [hslot] at heq
        have hc := transposedLayerPairSlot_mem (((bc ++ sc) ++ wc) ++ gc)
          (fwSeedJointLayerIndex bc sc wc gc hsc j k, e) s
        have hsafe := (hcols.transposed_support_safe _ hc).1
        have hr := layerPairSlot_mem (((br ++ sr) ++ wr) ++ gr) t side
        apply False.elim
        apply hsafe
        apply Finset.mem_union_right rect
        rw [heq]
        exact hr
  · intro ht
    obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp ht
    refine ⟨((j, prefixOrdinaryPairIndex hfit (0,k,e)),side), ?_⟩
    rw [fw_seed_existing_joint_row_match hseed hs choice br sr wr gr sc hsr hsc]
    exact (hslot _ side).symm

/-- For any set of row-network pairs containing the seed band, its actual
endpoint intersection with all selected seed cells is exactly the endpoint
image of the seed-band pairs. -/
theorem fw_seed_row_network_endpoint_overlap {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rect : Finset (Cell n))
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hrect : ∀ i side, packedRectangleCorner hs choice (i,side) ∈ rect)
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) a)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (U : Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n))
    (hU : fwSeedJointPairImage br sr wr gr hsr ⊆ U) :
    (Finset.univ.image (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)) ∩
      ((U.product (Finset.univ : Finset Bool)).image (rowNetworkSlot v)) =
    ((fwSeedJointPairImage br sr wr gr hsr).product (Finset.univ : Finset Bool)).image (rowNetworkSlot v) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨ha, hs'⟩ := Finset.mem_inter.mp hx
    obtain ⟨⟨t,side⟩, hts, rfl⟩ := Finset.mem_image.mp hs'
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
    have hrange : rowNetworkSlot v (t,side) ∈ Set.range
        (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) := ⟨i, hi⟩
    have ht := (fw_seed_row_network_slot_iff hseed hs choice rect br bc sr sc wr wc gr gc hsr hsc
      hrect hrows hcols v hslot t side).mp hrange
    exact Finset.mem_image.mpr ⟨(t,side), Finset.mem_product.mpr ⟨ht, Finset.mem_univ _⟩, rfl⟩
  · intro hx
    obtain ⟨⟨t,side⟩, hts, rfl⟩ := Finset.mem_image.mp hx
    have ht := (Finset.mem_product.mp hts).1
    have hrange := (fw_seed_row_network_slot_iff hseed hs choice rect br bc sr sc wr wc gr gc hsr hsc
      hrect hrows hcols v hslot t side).mpr ht
    obtain ⟨i, hi⟩ := hrange
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
    · exact Finset.mem_image.mpr ⟨(t,side), Finset.mem_product.mpr ⟨hU ht, Finset.mem_univ _⟩, rfl⟩

/-- A transposed packed column-layer endpoint lies in the full offset
seed-cell image exactly when its pair index is in the column seed band. -/
theorem fw_seed_column_layer_slot_iff {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rect : Finset (Cell n))
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hrect : ∀ i side, packedRectangleCorner hs choice (i,side) ∈ rect)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    (t : Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (side : Bool) :
    (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side).swap ∈
      Set.range (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) ↔
      t ∈ fwSeedJointPairImage bc sc wc gc hsc := by
  classical
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  constructor
  · rintro ⟨⟨⟨j,q⟩, s⟩, heq⟩
    obtain ⟨tag, htag⟩ := (prefixStagePairSlot_bijective hfit hdiag hexact).2 q
    rw [← htag] at heq
    cases tag with
    | inl z =>
      rcases z with ⟨i, pair⟩
      simp only [prefixStagePairSlot] at heq
      rw [fw_seed_existing_rectangle_cell] at heq
      have hm := hrect (fwSeedRectangle hseed (finProdFinEquiv (j,i))) (prefixPairCorner pair s)
      have hc := transposedLayerPairSlot_mem (((bc ++ sc) ++ wc) ++ gc) t side
      have hsafe := (hcols.transposed_support_safe _ hc).1
      apply False.elim
      apply hsafe
      apply Finset.mem_union_left
      rw [← heq]
      exact hm
    | inr z =>
      rcases z with ⟨net, k, e⟩
      fin_cases net
      · simp only [prefixStagePairSlot] at heq
        change fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
          ((j, prefixOrdinaryPairIndex hfit ((0 : Fin 2), k, e)), s) =
            (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side).swap at heq
        rw [fw_seed_existing_joint_row_match hseed hs choice br sr wr gr sc hsr hsc] at heq
        have hc := transposedLayerPairSlot_mem (((bc ++ sc) ++ wc) ++ gc) t side
        have hsafe := (hcols.transposed_support_safe _ hc).1
        have hr := layerPairSlot_mem (((br ++ sr) ++ wr) ++ gr)
          (fwSeedJointLayerIndex br sr wr gr hsr j k, e) s
        apply False.elim
        apply hsafe
        apply Finset.mem_union_right rect
        rw [← heq]
        exact hr
      · simp only [prefixStagePairSlot] at heq
        change fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
          ((j, prefixOrdinaryPairIndex hfit ((1 : Fin 2), k, e)), s) =
            (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side).swap at heq
        rw [fw_seed_existing_joint_column_match hseed hs choice sr bc sc wc gc hsr hsc] at heq
        have hsides := congrArg Prod.swap heq
        simp only [Prod.swap_swap] at hsides
        have hi := hcols.sequenceCell_injective hsides
        have hfirst := congrArg (fun z : Fin (((bc ++ sc) ++ wc) ++ gc).length × (Fin n × Bool) => z.1) hi
        have hvertex := congrArg (fun z : Fin (((bc ++ sc) ++ wc) ++ gc).length × (Fin n × Bool) => z.2.1) hi
        exact Finset.mem_image.mpr ⟨((j,k),e), Finset.mem_univ _, Prod.ext hfirst hvertex⟩
  · intro ht
    obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨((j, prefixOrdinaryPairIndex hfit (1,k,e)),side),
      fw_seed_existing_joint_column_match hseed hs choice sr bc sc wc gc hsr hsc j k e side⟩

/-- The selected seed-cell intersection with any physical column-network
endpoint image containing the seed band is exactly that seed-band endpoint
image. Both sides use original, untransposed square coordinates. -/
theorem fw_seed_column_network_endpoint_overlap {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rect : Finset (Cell n))
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hrect : ∀ i side, packedRectangleCorner hs choice (i,side) ∈ rect)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    (U : Finset (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n))
    (hU : fwSeedJointPairImage bc sc wc gc hsc ⊆ U) :
    (Finset.univ.image (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)) ∩
      ((U.product (Finset.univ : Finset Bool)).image
        (fun x => (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) x.1 x.2).swap)) =
    ((fwSeedJointPairImage bc sc wc gc hsc).product (Finset.univ : Finset Bool)).image
      (fun x => (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) x.1 x.2).swap) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨ha, hs'⟩ := Finset.mem_inter.mp hx
    obtain ⟨⟨t,side⟩, hts, rfl⟩ := Finset.mem_image.mp hs'
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
    have hrange : (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side).swap ∈ Set.range
        (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) := ⟨i, hi⟩
    have ht := (fw_seed_column_layer_slot_iff hseed hs choice rect br bc sr sc wr wc gr gc hsr hsc
      hrect hcols t side).mp hrange
    exact Finset.mem_image.mpr ⟨(t,side), Finset.mem_product.mpr ⟨ht, Finset.mem_univ _⟩, rfl⟩
  · intro hx
    obtain ⟨⟨t,side⟩, hts, rfl⟩ := Finset.mem_image.mp hx
    have ht := (Finset.mem_product.mp hts).1
    have hrange := (fw_seed_column_layer_slot_iff hseed hs choice rect br bc sr sc wr wc gr gc hsr hsc
      hrect hcols t side).mpr ht
    obtain ⟨i, hi⟩ := hrange
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
    · exact Finset.mem_image.mpr ⟨(t,side), Finset.mem_product.mpr ⟨hU ht, Finset.mem_univ _⟩, rfl⟩

/-- The canonical packed-rectangle reservation supplies all rectangle
corners required by the two endpoint-overlap results. -/
theorem fw_seed_reserved_rectangle_corners {n L : ℕ}
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (rect : Finset (Cell n))
    (hrect : packedRectangleSupport hs choice ⊆ rect) :
    ∀ i side, packedRectangleCorner hs choice (i,side) ∈ rect := by
  intro i side
  apply hrect
  exact Finset.mem_image.mpr ⟨(i,side), Finset.mem_univ _, rfl⟩

/-- Exact selected-seed overlap for the union of all blocks of the actual
centered row network. The rectangle reservation must contain all packed
rectangle corners, and the block identity must use the joint seed support. -/
theorem fw_seed_centered_row_endpoint_overlap {n L P : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rect : Finset (Cell n))
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (hrect : packedRectangleSupport hs choice ⊆ rect)
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) a)
    (B : CenteredNetwork (Fin 3 × Fin n) (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) v)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hblock : ∀ edge, B.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2))) :
    (Finset.univ.image (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)) ∩
      (((Finset.univ.biUnion B.block).product (Finset.univ : Finset Bool)).image (rowNetworkSlot v)) =
    ((fwSeedJointPairImage br sr wr gr hsr).product (Finset.univ : Finset Bool)).image (rowNetworkSlot v) := by
  exact fw_seed_row_network_endpoint_overlap hseed hs choice rect br bc sr sc wr wc gr gc hsr hsc
    (fw_seed_reserved_rectangle_corners hs choice rect hrect) hrows hcols v hslot
    (Finset.univ.biUnion B.block)
    (fw_seed_joint_image_subset_blocks br sr wr gr hbr hsr hwr hgr B.block hblock)

/-- The same exact overlap for the actual centered column network, stated in
original square coordinates. -/
theorem fw_seed_centered_column_endpoint_overlap {n L P : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rect : Finset (Cell n))
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbc : bc.length = 5 * 3) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (hgc : gc.length = P * 3)
    (hrect : packedRectangleSupport hs choice ⊆ rect)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n)
      (LayerPacking.transposePlacement a))
    (B : CenteredNetwork (Fin 3 × Fin n) (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) v)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (hblock : ∀ edge, B.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2))) :
    (Finset.univ.image (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)) ∩
      (((Finset.univ.biUnion B.block).product (Finset.univ : Finset Bool)).image
        (fun x => (rowNetworkSlot v x).swap)) =
    ((fwSeedJointPairImage bc sc wc gc hsc).product (Finset.univ : Finset Bool)).image
      (fun x => (rowNetworkSlot v x).swap) := by
  have h := fw_seed_column_network_endpoint_overlap hseed hs choice rect br bc sr sc wr wc gr gc hsr hsc
    (fw_seed_reserved_rectangle_corners hs choice rect hrect) hcols
    (Finset.univ.biUnion B.block)
    (fw_seed_joint_image_subset_blocks bc sc wc gc hbc hsc hwc hgc B.block hblock)
  simp_rw [← hslot] at h
  exact h

end
end Sude
