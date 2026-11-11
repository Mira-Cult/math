import Sude.FWSeedOffsetActualRowColumn
import Sude.FWJointSupportedIndex

/-! Side-preserving identification of actual offset seed ordinary pairs with
the seed band of the joint row/column layer lists. Rectangle and perpendicular
ordinary labels remain distinct. No centered-square conclusion is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- The actual seed row pair agrees, side for side, with the seed-band pair
in the combined row layer list. -/
theorem fw_seed_existing_joint_row_match {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (br sr wr gr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (j : Fin 16) (k : Fin 3) (e : Fin n) (side : Bool) :
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (0, k, e)), side) =
      layerPairSlot (((br ++ sr) ++ wr) ++ gr)
        (fwSeedJointLayerIndex br sr wr gr hsr j k, e) side := by
  rw [fw_seed_existing_row_cell]
  rw [fw_seed_joint_row_cell br sr wr gr sc hsr hsc]
  simp [fwSeedEdgeCells, fwSeedOrdinaryCells, LayerPacking.sequenceCell,
    prefixStageLayer]

/-- The analogous column identification is stated in the original square's
coordinates, so the joint column-layer slot is explicitly transposed. -/
theorem fw_seed_existing_joint_column_match {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr bc sc wc gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (j : Fin 16) (k : Fin 3) (e : Fin n) (side : Bool) :
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (1, k, e)), side) =
      (layerPairSlot (((bc ++ sc) ++ wc) ++ gc)
        (fwSeedJointLayerIndex bc sc wc gc hsc j k, e) side).swap := by
  rw [fw_seed_existing_column_cell]
  rw [fw_seed_joint_column_cell sr bc sc wc gc hsr hsc]
  simp [fwSeedEdgeCells, fwSeedOrdinaryCells, LayerPacking.sequenceCell,
    prefixStageLayer]

/-- At any stages, row-ordinary and column-ordinary seed labels cannot name
the same pair slot. -/
theorem fw_seed_ordinary_network_labels_separate {n : ℕ}
    (j j' : Fin 16) (k k' : Fin 3) (e e' : Fin n) :
    (j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (0, k, e)) ≠
    (j', prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (1, k', e')) := by
  intro h
  have hi := congrArg Prod.snd h
  have he := prefixOrdinaryPairIndex_injective (by omega) hi
  have hn := congrArg Prod.fst he
  have hf : (0 : Fin 2) = 1 := hn
  exact (by decide : (0 : Fin 2) ≠ 1) hf

/-- An ordinary seed pair label cannot be a diagonal-rectangle pair label,
including the second rectangle pair whose endpoint-corner order is reversed. -/
theorem fw_seed_ordinary_rectangle_labels_separate {n : ℕ}
    (j j' : Fin 16) (net : Fin 2) (k : Fin 3) (e : Fin n)
    (rect : Fin (4 * 6)) (pair : Fin 2) :
    (j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (net, k, e)) ≠
    (j', prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect, pair)) := by
  intro h
  exact prefixOrdinary_ne_diagonal (by omega) (by omega) (net, k, e) (rect, pair)
    (congrArg Prod.snd h)

/-- All actual combined-list ordinary seed pair indices, across stages,
network layers and graph vertices. -/
def fwSeedJointPairImage {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) : Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) :=
  Finset.univ.image (fun x : (Fin 16 × Fin 3) × Fin n =>
    (fwSeedJointLayerIndex br sr wr gr hsr x.1.1 x.1.2, x.2))

/-- Every seed-band pair belongs to the block for its own graph edge when
the blocks use the actual joint supported-label interface. -/
theorem fw_seed_joint_pair_mem_actual_block {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (blocks : (Fin 3 × Fin n) → Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n))
    (hblock : ∀ edge, blocks edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (j : Fin 16) (k : Fin 3) (e : Fin n) :
    (fwSeedJointLayerIndex br sr wr gr hsr j k, e) ∈ blocks (k,e) := by
  classical
  rw [hblock]
  let tag : FWJointGridTag n P := Sum.inl (Sum.inl (Sum.inl j))
  have htag : tag ∈ fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450)) := by
    simp [tag, fwJointGridLabels, fwJointPreWideGridLabels]
  refine Finset.mem_image.mpr ⟨⟨tag, htag⟩, Finset.mem_attach _ _, ?_⟩
  rfl

/-- The full seed-band image is contained in the union of the actual edge
blocks. It does not say that any nonseed label belongs to that image. -/
theorem fw_seed_joint_image_subset_blocks {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (blocks : (Fin 3 × Fin n) → Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n))
    (hblock : ∀ edge, blocks edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2))) :
    fwSeedJointPairImage br sr wr gr hsr ⊆ Finset.univ.biUnion blocks := by
  classical
  intro x hx
  obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_biUnion.mpr ⟨(k,e), Finset.mem_univ _,
    fw_seed_joint_pair_mem_actual_block br sr wr gr hbr hsr hwr hgr blocks hblock j k e⟩

/-- Decode a seed-band joint pair to the corresponding ordinary pair slot.
The default outside the seed image has no semantic significance. -/
def fwSeedJointToOrdinaryIndex {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (net : Fin 2)
    (t : Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) : Fin 16 × Fin (6 * (n + 8)) := by
  classical
  let f := fun x : (Fin 16 × Fin 3) × Fin n =>
    (fwSeedJointLayerIndex br sr wr gr hsr x.1.1 x.1.2, x.2)
  exact if h : ∃ x, f x = t then
    let x := Classical.choose h
    (x.1.1, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (net, x.1.2, x.2))
  else (0, 0)

/-- The decoder recovers the same stage, network-layer and vertex on every
seed-band joint pair. -/
theorem fw_seed_joint_to_ordinary_index {n : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (net : Fin 2) (j : Fin 16) (k : Fin 3) (e : Fin n) :
    fwSeedJointToOrdinaryIndex br sr wr gr hsr net
      (fwSeedJointLayerIndex br sr wr gr hsr j k, e) =
    (j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (net, k, e)) := by
  classical
  unfold fwSeedJointToOrdinaryIndex
  dsimp only
  split_ifs with h
  · have he := Classical.choose_spec h
    have he' : (fun x : (Fin 16 × Fin 3) × Fin n =>
        (fwSeedJointLayerIndex br sr wr gr hsr x.1.1 x.1.2, x.2)) (Classical.choose h) =
        (fun x : (Fin 16 × Fin 3) × Fin n =>
          (fwSeedJointLayerIndex br sr wr gr hsr x.1.1 x.1.2, x.2)) ((j,k),e) := he
    have hx := fwSeedJointPairIndex_injective br sr wr gr hsr he'
    rw [hx]
  · exact False.elim (h ⟨((j,k),e), rfl⟩)

/-- The decoded row-network slots match both physical sides of every pair in
the seed-band image, for any row network exposing the stated joint slots. -/
theorem fw_seed_joint_row_side_matching {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (br sr wr gr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) a)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side) :
    ∀ t ∈ fwSeedJointPairImage br sr wr gr hsr,
      fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
          (fwSeedJointToOrdinaryIndex br sr wr gr hsr 0 t, false) = (v.low t, v.column t) ∧
      fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
          (fwSeedJointToOrdinaryIndex br sr wr gr hsr 0 t, true) = (v.high t, v.column t) := by
  classical
  intro t ht
  obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp ht
  rw [fw_seed_joint_to_ordinary_index]
  constructor
  · have hm := fw_seed_existing_joint_row_match hseed hs choice br sr wr gr sc hsr hsc j k e false
    rw [← hslot] at hm
    simpa [rowNetworkSlot] using hm
  · have hm := fw_seed_existing_joint_row_match hseed hs choice br sr wr gr sc hsr hsc j k e true
    rw [← hslot] at hm
    simpa [rowNetworkSlot] using hm

/-- In transposed coordinates the same side-preserving match applies to the
column network. -/
theorem fw_seed_joint_column_side_matching {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr bc sc wc gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n)
      (LayerPacking.transposePlacement a))
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side) :
    ∀ t ∈ fwSeedJointPairImage bc sc wc gc hsc,
      (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
          (fwSeedJointToOrdinaryIndex bc sc wc gc hsc 1 t, false)).swap = (v.low t, v.column t) ∧
      (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
          (fwSeedJointToOrdinaryIndex bc sc wc gc hsc 1 t, true)).swap = (v.high t, v.column t) := by
  classical
  intro t ht
  obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp ht
  rw [fw_seed_joint_to_ordinary_index]
  constructor
  · have hm := congrArg Prod.swap (fw_seed_existing_joint_column_match hseed hs choice sr bc sc wc gc hsr hsc j k e false)
    simp only [Prod.swap_swap] at hm
    rw [← hslot] at hm
    simpa [rowNetworkSlot] using hm
  · have hm := congrArg Prod.swap (fw_seed_existing_joint_column_match hseed hs choice sr bc sc wc gc hsr hsc j k e true)
    simp only [Prod.swap_swap] at hm
    rw [← hslot] at hm
    simpa [rowNetworkSlot] using hm

/-- The decoder is injective on the complete seed-band image. It need not
be injective on any nonseed indices, where its default is unconstrained. -/
theorem fw_seed_joint_to_ordinary_injective_on_image {n : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (net : Fin 2) :
    Set.InjOn (fwSeedJointToOrdinaryIndex br sr wr gr hsr net)
      {t | t ∈ fwSeedJointPairImage br sr wr gr hsr} := by
  classical
  intro t ht t' ht' heq
  change t ∈ fwSeedJointPairImage br sr wr gr hsr at ht
  change t' ∈ fwSeedJointPairImage br sr wr gr hsr at ht'
  unfold fwSeedJointPairImage at ht ht'
  obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨⟨⟨j',k'⟩,e'⟩, _, rfl⟩ := Finset.mem_image.mp ht'
  rw [fw_seed_joint_to_ordinary_index, fw_seed_joint_to_ordinary_index] at heq
  have hj := congrArg Prod.fst heq
  have hi := prefixOrdinaryPairIndex_injective (by omega) (congrArg Prod.snd heq)
  have hke := congrArg Prod.snd hi
  cases hj
  cases hke
  rfl

/-- The packed-row network exposes the corresponding layer-pair slot with
the same endpoint side. -/
theorem fw_packed_row_network_slot {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (LayerPacking.Layer n)} (packed : LayerPacking.PackedLayers reserved layers)
    (a : Cell n ≃ Fin (n*n)) (gap : Fin layers.length → Fin n → ℕ)
    (hgap : ∀ i e, entry a ((layers.get i).1 e, (layers.get i).2 e) =
      entry a (e, (layers.get i).2 e) + gap i e)
    (t : Fin layers.length × Fin n) (side : Bool) :
    rowNetworkSlot (packed.rowPairs a gap hgap) (t,side) = layerPairSlot layers t side := by
  cases t
  cases side <;> rfl

/-- The packed-column network is a row network on the transposed square and
exposes the untransposed layer slot in those transposed coordinates. -/
theorem fw_packed_column_network_slot {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (LayerPacking.Layer n)}
    (packed : LayerPacking.PackedLayers (LayerPacking.transposeCells reserved) layers)
    (a : Cell n ≃ Fin (n*n)) (gap : Fin layers.length → Fin n → ℕ)
    (hgap : ∀ i e, entry a ((layers.get i).2 e, (layers.get i).1 e) =
      entry a ((layers.get i).2 e, e) + gap i e)
    (t : Fin layers.length × Fin n) (side : Bool) :
    rowNetworkSlot (packed.columnPairs a gap hgap) (t,side) = layerPairSlot layers t side := by
  cases t
  cases side <;> rfl

/-- If all seed cells are injective, the row and column ordinary families
have disjoint physical endpoints, including across different stages. -/
theorem fw_seed_ordinary_network_cells_separate {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hcells : Function.Injective (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc))
    (j j' : Fin 16) (k k' : Fin 3) (e e' : Fin n) (side side' : Bool) :
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (0,k,e)), side) ≠
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j', prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (1,k',e')), side') := by
  intro h
  exact fw_seed_ordinary_network_labels_separate j j' k k' e e'
    (congrArg Prod.fst (hcells h))

/-- An ordinary seed endpoint cannot coincide with any seed rectangle-pair
endpoint when the actual seed cell map is injective. -/
theorem fw_seed_ordinary_rectangle_cells_separate {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hcells : Function.Injective (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc))
    (j j' : Fin 16) (net : Fin 2) (k : Fin 3) (e : Fin n)
    (rect : Fin (4 * 6)) (pair : Fin 2) (side side' : Bool) :
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (net,k,e)), side) ≠
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j', prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair)), side') := by
  intro h
  exact fw_seed_ordinary_rectangle_labels_separate j j' net k e rect pair
    (congrArg Prod.fst (hcells h))

end
end Sude
