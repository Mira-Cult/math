import Sude.FWBridgeSeedWideRolePreservation

/-! Exact endpoint coverage for bridge and retained-seed role families. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem fwBridge_reservation_eq_endpoints (n : ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j) :
    Finset.univ.image (fwBridgeStageEndpoint n ∅ batches hvalid) =
      priorBridgeReservation ∅ (Finset.range 5) batches := by
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    exact fwBridgeStageEndpoint_mem_final_reservation n batches hvalid x
  · intro p hp
    simp only [priorBridgeReservation, stagedReservation, Finset.empty_union,
      Finset.mem_biUnion, Finset.mem_range, Finset.mem_union, doubleBatchLow,
      doubleBatchHigh, Finset.mem_insert, Finset.mem_singleton, List.mem_toFinset] at hp
    obtain ⟨j, hj, hp⟩ := hp
    rcases hp with ⟨b, hb, hp⟩ | ⟨b, hb, hp⟩ <;>
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hb <;>
      have hlen := (hvalid j hj).1.1 <;>
      let k : Fin (3 * (n + 8)) := ⟨i, by simpa [← hlen] using i.isLt⟩ <;>
      have hblock : fwBridgeStageBlock n ∅ batches hvalid ⟨j, hj⟩ k = b := hi <;>
      rcases hp with hp | hp
    · exact Finset.mem_image.mpr ⟨((⟨j, hj⟩, k), 0), Finset.mem_univ _, by simpa [fwBridgeStageEndpoint, hblock, DoublePair.endpoint] using hp.symm⟩
    · exact Finset.mem_image.mpr ⟨((⟨j, hj⟩, k), 3), Finset.mem_univ _, by simpa [fwBridgeStageEndpoint, hblock, DoublePair.endpoint] using hp.symm⟩
    · exact Finset.mem_image.mpr ⟨((⟨j, hj⟩, k), 1), Finset.mem_univ _, by simpa [fwBridgeStageEndpoint, hblock, DoublePair.endpoint] using hp.symm⟩
    · exact Finset.mem_image.mpr ⟨((⟨j, hj⟩, k), 2), Finset.mem_univ _, by simpa [fwBridgeStageEndpoint, hblock, DoublePair.endpoint] using hp.symm⟩

/-- Exact role equations and surjective indexing locate every value in the
reserved set at one of the supplied physical role cells. -/
theorem protectedPoolCells_subset_role_images {n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] (a : Cell n ≃ Fin (n*n))
    (bridge seed : Finset ℕ) (bc : ι → Cell n) (sc : κ → Cell n)
    (bv : ι → ℕ) (sv : κ → ℕ)
    (hb : Finset.univ.image bv = bridge) (hs : Finset.univ.image sv = seed)
    (hbp : ∀ i, entry a (bc i) = bv i) (hsp : ∀ i, entry a (sc i) = sv i) :
    protectedPoolCells a (bridge ∪ seed) ⊆
      Finset.univ.image bc ∪ Finset.univ.image sc := by
  intro c hc
  have hv := (mem_protectedPoolCells a _ c).mp hc
  rcases Finset.mem_union.mp hv with hv | hv
  · rw [← hb] at hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    have heq : bc i = c := (entry_injective a) ((hbp i).trans hi)
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩)
  · rw [← hs] at hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    have heq : sc i = c := (entry_injective a) ((hsp i).trans hi)
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩)

/-- The four physical endpoint equations cover every reserved bridge and
retained seed value. No geometric inclusion is assumed. -/
theorem fw_bridge_seed_protected_covered {n L : ℕ}
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (a : Cell n ≃ Fin (n*n))
    (hbd : ∀ t side, entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hbo : ∀ x, entry a (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (hsd : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry a (packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept
          (prefixRectangleInput (by omega) x)))
    (hso : ∀ x, entry a (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x))) :
    protectedPoolCells a (fwBridgeSeedProtectedValues batches candidates hcard kept hsub) ⊆
      (Finset.univ.image (fun x : Fin (5 * (4 * 6)) × Fin 4 =>
        packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect x.1, x.2)) ∪
       Finset.univ.image (fwBridgeLayerCells rows cols hr hc)) ∪
      (Finset.univ.image (fun x : Fin (16 * (4 * 6)) × Fin 4 =>
        packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) ∪
       Finset.univ.image (fwSeedOrdinaryCells sr sc hsr hsc)) := by
  let bc : (Fin (5 * (4 * 6)) × Fin 4) ⊕
      ((Fin 5 × (Fin 3 × Fin n)) × (Bool × Bool)) → Cell n :=
    Sum.elim (fun x => packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect x.1, x.2))
      (fwBridgeLayerCells rows cols hr hc)
  let si : PrefixPhysicalInputs 16 6 3 n → (Fin 16 × Fin (6 * (n + 8))) × Bool :=
    prefixPhysicalInput (by omega) (by omega)
  let scell : PrefixPhysicalInputs 16 6 3 n → Cell n :=
    Sum.elim (fun x => packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2))
      (fwSeedOrdinaryCells sr sc hsr hsc)
  let bv := fun x => fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeControllerSlot n x)
  let sv := fun x => sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
      (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (si x))
  have hb : Finset.univ.image bv = priorBridgeReservation ∅ (Finset.range 5) batches := by
    change Finset.univ.image ((fwBridgeStageEndpoint n ∅ batches hvalid) ∘ fwBridgeControllerSlot n) = _
    rw [← Finset.image_image, Finset.image_univ_of_surjective (fwBridgeControllerSlot_bijective n).2]
    exact fwBridge_reservation_eq_endpoints n batches hvalid
  have hse : Finset.univ.image sv = retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub := by
    dsimp [sv, si]
    exact prefixPhysicalInput_retained_image candidates 17 16 (6 * (n + 8)) 2 6 3 n
      hcard kept hsub hkept hinj (by omega) (by omega) (by omega)
  have hbp : ∀ x, entry a (bc x) = bv x := by
    intro x
    cases x with
    | inl x => exact hbd x.1 x.2
    | inr x => exact hbo x
  have hsp : ∀ x, entry a (scell x) = sv x := by
    intro x
    cases x with
    | inl x => exact hsd x
    | inr x =>
      cases x with
      | inl x => exact hso (Sum.inl x)
      | inr x => exact hso (Sum.inr x)
  have hcov := protectedPoolCells_subset_role_images a _ _ bc scell bv sv hb hse hbp hsp
  intro c hc'
  have hm := hcov hc'
  rcases Finset.mem_union.mp hm with hb' | hs'
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hb'
    cases x with
    | inl x => exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))
    | inr x => exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hs'
    cases x with
    | inl x => exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))
    | inr x => exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))

/-- The actual role images lie in the full bridge-and-seed packing base. -/
theorem fw_bridge_seed_role_images_subset_base {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) :
    (Finset.univ.image (fun x : Fin (5 * (4 * 6)) × Fin 4 =>
      packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect x.1, x.2)) ∪
     Finset.univ.image (fwBridgeLayerCells rows cols hr hc)) ∪
    (Finset.univ.image (fun x : Fin (16 * (4 * 6)) × Fin 4 =>
      packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) ∪
     Finset.univ.image (fwSeedOrdinaryCells sr sc hsr hsc)) ⊆
      (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪
        LayerPacking.layersSupport sr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc) := by
  intro c hc'
  have hrectmem : ∀ (t : Fin L) side, packedRectangleCorner hs choice (t, side) ∈ packedRectangleSupport hs choice := by
    intro t side
    exact Finset.mem_image.mpr ⟨(t, side), Finset.mem_univ _, rfl⟩
  have hrowmem : ∀ (rs : List (LayerPacking.Layer n)) x,
      LayerPacking.sequenceCell rs x ∈ LayerPacking.layersSupport rs := by
    intro rs x
    exact LayerPacking.layerSupport_subset _ rs (List.get_mem rs x.1) (LayerPacking.sequenceCell_mem rs x.1 x.2)
  have hcolmem : ∀ (rs : List (LayerPacking.Layer n)) x,
      (LayerPacking.sequenceCell rs x).swap ∈ LayerPacking.transposeCells (LayerPacking.layersSupport rs) := by
    intro rs x
    exact Finset.mem_image.mpr ⟨_, hrowmem rs x, rfl⟩
  rcases Finset.mem_union.mp hc' with hb | hs'
  · rcases Finset.mem_union.mp hb with hd | ho
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hrectmem _ _))))
    · obtain ⟨⟨x, ⟨net, side⟩⟩, _, rfl⟩ := Finset.mem_image.mp ho
      cases net
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hrowmem rows _))))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hcolmem cols _)))
  · rcases Finset.mem_union.mp hs' with hd | ho
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hrectmem _ _))))
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ho
      cases x with
      | inl x => exact Finset.mem_union_left _ (Finset.mem_union_right _ (hrowmem sr _))
      | inr x => exact Finset.mem_union_right _ (hcolmem sc _)

/-- Wide rectangle corners avoid all four actual earlier role families. -/
theorem fw_wide_corner_avoids_bridge_seed_roles {n L J : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hsrows : LayerPacking.PackedLayers
      ((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) sr)
    (hscols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr)) sc)
    (hsdisj : Disjoint (LayerPacking.layersSupport sr) (LayerPacking.transposeCells (LayerPacking.layersSupport sc)))
    (x : Fin (J * (4 * 6)) × Fin 4) :
    packedRectangleCorner hs choice (fwWideRectangle hwide x.1, x.2) ∉
      (Finset.univ.image (fun x : Fin (5 * (4 * 6)) × Fin 4 =>
        packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect x.1, x.2)) ∪
       Finset.univ.image (fwBridgeLayerCells rows cols hr hc)) ∪
      (Finset.univ.image (fun x : Fin (16 * (4 * 6)) × Fin 4 =>
        packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) ∪
       Finset.univ.image (fwSeedOrdinaryCells sr sc hsr hsc)) := by
  have hmem : packedRectangleCorner hs choice (fwWideRectangle hwide x.1, x.2) ∈ packedRectangleSupport hs choice :=
    Finset.mem_image.mpr ⟨(fwWideRectangle hwide x.1, x.2), Finset.mem_univ _, rfl⟩
  have hbridgefree : ∀ y, fwBridgeLayerCells rows cols hr hc y ∉ packedRectangleSupport hs choice := by
    rintro ⟨a, ⟨net, side⟩⟩
    cases net
    · exact hrows.sequenceCell_unreserved _
    · have hcmem : (LayerPacking.sequenceCell cols (fwBridgeLayerIndex hc (a, side))).swap ∈
          LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
        apply Finset.mem_image.mpr
        exact ⟨_, LayerPacking.layerSupport_subset _ cols (List.get_mem cols _)
          (LayerPacking.sequenceCell_mem cols _ _), rfl⟩
      intro hz
      exact (hcols.transposed_support_safe _ hcmem).1 (Finset.mem_union_left _ hz)
  have hseedfree : ∀ y, fwSeedOrdinaryCells sr sc hsr hsc y ∉ packedRectangleSupport hs choice := by
    intro y hy
    have hbase : packedRectangleSupport hs choice ⊆
        ((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
      intro c hc'
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hc')
    exact (fwSeedOrdinaryCells_geometry hs choice _ hbase sr sc hsr hsc hsrows hscols hsdisj).2.1 y (hbase hy)
  intro hc'
  rcases Finset.mem_union.mp hc' with hb | hseed'
  · rcases Finset.mem_union.mp hb with hd | ho
    · obtain ⟨y, _, heq⟩ := Finset.mem_image.mp hd
      have he := (packedRectangleCorner_injective hs choice) heq
      exact (fw_bridge_wide_rectangle_ne hrect hwide y.1 x.1) (congrArg Prod.fst he)
    · obtain ⟨y, _, heq⟩ := Finset.mem_image.mp ho
      exact hbridgefree y (heq ▸ hmem)
  · rcases Finset.mem_union.mp hseed' with hd | ho
    · obtain ⟨y, _, heq⟩ := Finset.mem_image.mp hd
      have he := (packedRectangleCorner_injective hs choice) heq
      exact (fw_seed_wide_rectangle_ne hseed hwide y.1 x.1) (congrArg Prod.fst he)
    · obtain ⟨y, _, heq⟩ := Finset.mem_image.mp ho
      exact hseedfree y (heq ▸ hmem)

end
end Sude
