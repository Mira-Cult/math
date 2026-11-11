import Sude.FWPermutedOrdinaryEdgeGaps
import Sude.FWSeedNetworkMatching

/-! Actual bridge and wide ordinary-network slot images, decoders, and
side-preserving physical matches. Unmatched pair labels remain explicit. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- The actual bridge band of a joint row or transposed-column list. -/
def fwBridgeJointPairImage {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) : Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) :=
  Finset.univ.image (fun x : (Fin 5 × Fin 3) × Fin n =>
    (fwBridgeJointLayerIndex br sr wr gr hbr x.1.1 x.1.2, x.2))

/-- The actual wide band of a joint row or transposed-column list. -/
def fwWideJointPairImage {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) : Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) :=
  Finset.univ.image (fun x : (Fin (3 * (n / 450)) × Fin 3) × Fin n =>
    (fwWideJointLayerIndex br sr wr gr hwr x.1.1 x.1.2, x.2))

/-- Decode actual bridge-band network slots to grouped controller labels.
The default outside the image is irrelevant. -/
def fwBridgeJointToGrouped {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (net : Fin 2)
    (t : Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) : Fin 5 × Fin (3 * (n + 8)) × Fin 2 := by
  classical
  let f := fun x : (Fin 5 × Fin 3) × Fin n =>
    (fwBridgeJointLayerIndex br sr wr gr hbr x.1.1 x.1.2, x.2)
  exact if h : ∃ x, f x = t then
    let x := Classical.choose h
    (x.1.1, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) (x.1.2,x.2), net)
  else (0, 0, net)

/-- Decode the wide band; the explicit positivity covers the total-map
fallback, which otherwise cannot exist for an empty wide stage type. -/
def fwWideJointToGrouped {n : ℕ} (hJ : 0 < 3 * (n / 450))
    (br sr wr gr : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3) (net : Fin 2)
    (t : Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) :
    Fin (3 * (n / 450)) × Fin (3 * (n + 8)) × Fin 2 := by
  classical
  let f := fun x : (Fin (3 * (n / 450)) × Fin 3) × Fin n =>
    (fwWideJointLayerIndex br sr wr gr hwr x.1.1 x.1.2, x.2)
  exact if h : ∃ x, f x = t then
    let x := Classical.choose h
    (x.1.1, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) (x.1.2,x.2), net)
  else (⟨0,hJ⟩, 0, net)

theorem fw_bridge_joint_to_grouped {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (net : Fin 2) (j : Fin 5) (k : Fin 3) (e : Fin n) :
    fwBridgeJointToGrouped br sr wr gr hbr net (fwBridgeJointLayerIndex br sr wr gr hbr j k,e) =
      (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) (k,e), net) := by
  classical
  unfold fwBridgeJointToGrouped
  dsimp only
  split_ifs with h
  · have he := Classical.choose_spec h
    have hx := fwBridgeJointPairIndex_injective br sr wr gr hbr (show
      (fun x : (Fin 5 × Fin 3) × Fin n => (fwBridgeJointLayerIndex br sr wr gr hbr x.1.1 x.1.2,x.2)) (Classical.choose h) =
      (fun x : (Fin 5 × Fin 3) × Fin n => (fwBridgeJointLayerIndex br sr wr gr hbr x.1.1 x.1.2,x.2)) ((j,k),e) from he)
    rw [hx]
  · exact False.elim (h ⟨((j,k),e), rfl⟩)

theorem fw_wide_joint_to_grouped {n : ℕ} (hJ : 0 < 3 * (n / 450))
    (br sr wr gr : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (net : Fin 2) (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) :
    fwWideJointToGrouped hJ br sr wr gr hwr net (fwWideJointLayerIndex br sr wr gr hwr j k,e) =
      (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) (k,e), net) := by
  classical
  unfold fwWideJointToGrouped
  dsimp only
  split_ifs with h
  · have he := Classical.choose_spec h
    have hx := fwWideJointPairIndex_injective br sr wr gr hwr (show
      (fun x : (Fin (3 * (n / 450)) × Fin 3) × Fin n => (fwWideJointLayerIndex br sr wr gr hwr x.1.1 x.1.2,x.2)) (Classical.choose h) =
      (fun x : (Fin (3 * (n / 450)) × Fin 3) × Fin n => (fwWideJointLayerIndex br sr wr gr hwr x.1.1 x.1.2,x.2)) ((j,k),e) from he)
    rw [hx]
  · exact False.elim (h ⟨((j,k),e), rfl⟩)

/-- Both family decoders are injective on their actual band images. -/
theorem fw_bridge_joint_grouped_injective_on_image {n : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n)) (hbr : br.length = 5 * 3) (net : Fin 2) :
    Set.InjOn (fwBridgeJointToGrouped br sr wr gr hbr net) {t | t ∈ fwBridgeJointPairImage br sr wr gr hbr} := by
  classical
  intro t ht t' ht' heq
  change t ∈ fwBridgeJointPairImage br sr wr gr hbr at ht
  change t' ∈ fwBridgeJointPairImage br sr wr gr hbr at ht'
  obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨⟨⟨j',k'⟩,e'⟩, _, rfl⟩ := Finset.mem_image.mp ht'
  rw [fw_bridge_joint_to_grouped, fw_bridge_joint_to_grouped] at heq
  have hj := congrArg Prod.fst heq
  have hi := bridgeOrdinaryBlockIndex_injective (by omega) (congrArg (fun x => x.2.1) heq)
  cases hj
  cases hi
  rfl

theorem fw_wide_joint_grouped_injective_on_image {n : ℕ} (hJ : 0 < 3 * (n / 450))
    (br sr wr gr : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3) (net : Fin 2) :
    Set.InjOn (fwWideJointToGrouped hJ br sr wr gr hwr net) {t | t ∈ fwWideJointPairImage br sr wr gr hwr} := by
  classical
  intro t ht t' ht' heq
  change t ∈ fwWideJointPairImage br sr wr gr hwr at ht
  change t' ∈ fwWideJointPairImage br sr wr gr hwr at ht'
  obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨⟨⟨j',k'⟩,e'⟩, _, rfl⟩ := Finset.mem_image.mp ht'
  rw [fw_wide_joint_to_grouped, fw_wide_joint_to_grouped] at heq
  have hj := congrArg Prod.fst heq
  have hi := bridgeOrdinaryBlockIndex_injective (by omega) (congrArg (fun x => x.2.1) heq)
  cases hj
  cases hi
  rfl

/-- Every bridge-band slot belongs to the actual supported-label block of
its graph edge. -/
theorem fw_bridge_joint_image_subset_blocks {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (blocks : (Fin 3 × Fin n) → Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n))
    (hblock : ∀ edge, blocks edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2))) :
    fwBridgeJointPairImage br sr wr gr hbr ⊆ Finset.univ.biUnion blocks := by
  classical
  intro x hx
  obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_biUnion.mpr
  refine ⟨(k,e), Finset.mem_univ _, ?_⟩
  rw [hblock]
  let tag : FWJointGridTag n P := Sum.inl (Sum.inr j.val)
  have htag : tag ∈ fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450)) := by
    simp [tag, fwJointGridLabels, fwJointPreWideGridLabels, j.isLt]
  refine Finset.mem_image.mpr ⟨⟨tag, htag⟩, Finset.mem_attach _ _, ?_⟩
  rfl

/-- Every wide-band slot belongs to the actual supported-label block of its
own graph edge. This coverage theorem also permits an empty wide family. -/
theorem fw_wide_joint_image_subset_blocks {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (blocks : (Fin 3 × Fin n) → Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n))
    (hblock : ∀ edge, blocks edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2))) :
    fwWideJointPairImage br sr wr gr hwr ⊆ Finset.univ.biUnion blocks := by
  classical
  intro x hx
  obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_biUnion.mpr
  refine ⟨(k,e), Finset.mem_univ _, ?_⟩
  rw [hblock]
  let tag : FWJointGridTag n P := Sum.inr j
  have htag : tag ∈ fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450)) := by
    simp [tag, fwJointGridLabels]
  refine Finset.mem_image.mpr ⟨⟨tag, htag⟩, Finset.mem_attach _ _, ?_⟩
  rfl

/-- Bridge and wide band images are disjoint as joint network slots. This
does not by itself assert disjointness of their physical cell families. -/
theorem fw_bridge_wide_joint_images_disjoint {n : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hwr : wr.length = (3 * (n / 450)) * 3) :
    Disjoint (fwBridgeJointPairImage br sr wr gr hbr) (fwWideJointPairImage br sr wr gr hwr) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht hw
  obtain ⟨⟨⟨j,k⟩,e⟩, _, hte⟩ := Finset.mem_image.mp ht
  obtain ⟨⟨⟨j',k'⟩,e'⟩, _, htw⟩ := Finset.mem_image.mp hw
  have hi := congrArg (fun z => z.1.val) (hte.trans htw.symm)
  have hj := (finProdFinEquiv (j,k)).isLt
  simp only [fwBridgeJointLayerIndex, fwWideJointLayerIndex] at hi
  omega

/-- Grouped bridge row cells match the exact joint row slots side for side. -/
theorem fw_bridge_grouped_joint_row_match {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr bc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (j : Fin 5) (k : Fin 3) (e : Fin n) (side : Bool) :
    fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc
      ((j,bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) (k,e),0),side) =
      layerPairSlot (((br ++ sr) ++ wr) ++ gr) (fwBridgeJointLayerIndex br sr wr gr hr j k,e) side := by
  rw [fw_bridge_double_ordinary_cell, fw_bridge_joint_row_cell br sr wr gr bc hr hc]
  rfl

/-- Grouped bridge column cells match transposed joint column slots. -/
theorem fw_bridge_grouped_joint_column_match {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sc wc gc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (j : Fin 5) (k : Fin 3) (e : Fin n) (side : Bool) :
    fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc
      ((j,bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) (k,e),1),side) =
      (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (fwBridgeJointLayerIndex bc sc wc gc hc j k,e) side).swap := by
  rw [fw_bridge_double_ordinary_cell, fw_bridge_joint_column_cell br bc sc wc gc hr hc]
  rfl

/-- Grouped wide row cells match the exact joint row slots side for side. -/
theorem fw_wide_grouped_joint_row_match {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr wc : List (LayerPacking.Layer n)) (hr : wr.length = (3 * (n / 450)) * 3)
    (hc : wc.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (side : Bool) :
    fwWidePhysicalDoubleCells hwide hs choice wr wc hr hc
      ((j,bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) (k,e),0),side) =
      layerPairSlot (((br ++ sr) ++ wr) ++ gr) (fwWideJointLayerIndex br sr wr gr hr j k,e) side := by
  rw [fw_wide_double_ordinary_cell, fw_wide_joint_row_cell hwide hs choice br sr wr gr wc hr hc]
  rfl

/-- Grouped wide column cells match transposed joint column slots. -/
theorem fw_wide_grouped_joint_column_match {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (wr bc sc wc gc : List (LayerPacking.Layer n)) (hr : wr.length = (3 * (n / 450)) * 3)
    (hc : wc.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (side : Bool) :
    fwWidePhysicalDoubleCells hwide hs choice wr wc hr hc
      ((j,bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) (k,e),1),side) =
      (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (fwWideJointLayerIndex bc sc wc gc hc j k,e) side).swap := by
  rw [fw_wide_double_ordinary_cell, fw_wide_joint_column_cell hwide hs choice wr bc sc wc gc hr hc]
  rfl


/-- The selected bridge-band decoder matches both sides of the actual row
network slots. -/
theorem fw_bridge_joint_row_side_matching {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr bc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) a)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side) :
    ∀ t ∈ fwBridgeJointPairImage br sr wr gr hr,
      fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc (fwBridgeJointToGrouped br sr wr gr hr 0 t,false) = (v.low t,v.column t) ∧
      fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc (fwBridgeJointToGrouped br sr wr gr hr 0 t,true) = (v.high t,v.column t) := by
  classical
  intro t ht
  obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp ht
  rw [fw_bridge_joint_to_grouped]
  constructor
  · have h := fw_bridge_grouped_joint_row_match hrect hs choice br sr wr gr bc hr hc j k e false
    rw [← hslot] at h
    simpa [rowNetworkSlot] using h
  · have h := fw_bridge_grouped_joint_row_match hrect hs choice br sr wr gr bc hr hc j k e true
    rw [← hslot] at h
    simpa [rowNetworkSlot] using h

/-- In transposed coordinates the bridge decoder matches both column sides. -/
theorem fw_bridge_joint_column_side_matching {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sc wc gc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (LayerPacking.transposePlacement a))
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side) :
    ∀ t ∈ fwBridgeJointPairImage bc sc wc gc hc,
      (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc (fwBridgeJointToGrouped bc sc wc gc hc 1 t,false)).swap = (v.low t,v.column t) ∧
      (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc (fwBridgeJointToGrouped bc sc wc gc hc 1 t,true)).swap = (v.high t,v.column t) := by
  classical
  intro t ht
  obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp ht
  rw [fw_bridge_joint_to_grouped]
  constructor
  · have h := congrArg Prod.swap (fw_bridge_grouped_joint_column_match hrect hs choice br bc sc wc gc hr hc j k e false)
    simp only [Prod.swap_swap] at h
    rw [← hslot] at h
    simpa [rowNetworkSlot] using h
  · have h := congrArg Prod.swap (fw_bridge_grouped_joint_column_match hrect hs choice br bc sc wc gc hr hc j k e true)
    simp only [Prod.swap_swap] at h
    rw [← hslot] at h
    simpa [rowNetworkSlot] using h

/-- The selected wide-band decoder matches both actual row network sides. -/
theorem fw_wide_joint_row_side_matching {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (hJ : 0 < 3 * (n / 450))
    (br sr wr gr wc : List (LayerPacking.Layer n)) (hr : wr.length = (3 * (n / 450)) * 3)
    (hc : wc.length = (3 * (n / 450)) * 3)
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) a)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side) :
    ∀ t ∈ fwWideJointPairImage br sr wr gr hr,
      fwWidePhysicalDoubleCells hwide hs choice wr wc hr hc (fwWideJointToGrouped hJ br sr wr gr hr 0 t,false) = (v.low t,v.column t) ∧
      fwWidePhysicalDoubleCells hwide hs choice wr wc hr hc (fwWideJointToGrouped hJ br sr wr gr hr 0 t,true) = (v.high t,v.column t) := by
  classical
  intro t ht
  obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp ht
  rw [fw_wide_joint_to_grouped]
  constructor
  · have h := fw_wide_grouped_joint_row_match hwide hs choice br sr wr gr wc hr hc j k e false
    rw [← hslot] at h
    simpa [rowNetworkSlot] using h
  · have h := fw_wide_grouped_joint_row_match hwide hs choice br sr wr gr wc hr hc j k e true
    rw [← hslot] at h
    simpa [rowNetworkSlot] using h

/-- In transposed coordinates the wide decoder matches both column sides. -/
theorem fw_wide_joint_column_side_matching {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (hJ : 0 < 3 * (n / 450))
    (wr bc sc wc gc : List (LayerPacking.Layer n)) (hr : wr.length = (3 * (n / 450)) * 3)
    (hc : wc.length = (3 * (n / 450)) * 3)
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (LayerPacking.transposePlacement a))
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side) :
    ∀ t ∈ fwWideJointPairImage bc sc wc gc hc,
      (fwWidePhysicalDoubleCells hwide hs choice wr wc hr hc (fwWideJointToGrouped hJ bc sc wc gc hc 1 t,false)).swap = (v.low t,v.column t) ∧
      (fwWidePhysicalDoubleCells hwide hs choice wr wc hr hc (fwWideJointToGrouped hJ bc sc wc gc hc 1 t,true)).swap = (v.high t,v.column t) := by
  classical
  intro t ht
  obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp ht
  rw [fw_wide_joint_to_grouped]
  constructor
  · have h := congrArg Prod.swap (fw_wide_grouped_joint_column_match hwide hs choice wr bc sc wc gc hr hc j k e false)
    simp only [Prod.swap_swap] at h
    rw [← hslot] at h
    simpa [rowNetworkSlot] using h
  · have h := congrArg Prod.swap (fw_wide_grouped_joint_column_match hwide hs choice wr bc sc wc gc hr hc j k e true)
    simp only [Prod.swap_swap] at h
    rw [← hslot] at h
    simpa [rowNetworkSlot] using h

/-- The concrete rectangle geometry makes the wide decoder fallback valid. -/
theorem fw_wide_stage_count_pos_of_geometry {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) : 0 < 3 * (n / 450) := by omega

end
end Sude
