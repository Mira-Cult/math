import Sude.FWSeedExistingReallocation

namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Seed reallocation fixes the separately packed bridge rectangle and ordinary roles. -/
theorem fw_seed_reallocation_preserves_bridge_roles {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols sr sc : List (LayerPacking.Layer n))
    (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols)
    (hsrows : LayerPacking.PackedLayers
      ((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) sr)
    (hscols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪
          LayerPacking.layersSupport sr)) sc)
    (grown b : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c, c ∉ Set.range (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) →
      entry b c = entry grown c) :
    (∀ t side, entry b (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      entry grown (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side))) ∧
    (∀ x, entry b (fwBridgeLayerCells rows cols hr hc x) =
      entry grown (fwBridgeLayerCells rows cols hr hc x)) := by
  classical
  let rect := packedRectangleSupport hs choice
  let base := (rect ∪ LayerPacking.layersSupport rows) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  let prior : Finset (Cell n) :=
    Finset.univ.image (fun x : Fin (5 * (4 * 6)) × Fin 4 =>
      packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect x.1, x.2)) ∪
    Finset.univ.image (fwBridgeLayerCells rows cols hr hc)
  have hrowmem : ∀ x, LayerPacking.sequenceCell rows x ∈ LayerPacking.layersSupport rows := by
    intro x
    exact LayerPacking.layerSupport_subset _ rows (List.get_mem rows _) (LayerPacking.sequenceCell_mem rows _ _)
  have hcolmem : ∀ x, (LayerPacking.sequenceCell cols x).swap ∈
      LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
    intro x
    exact Finset.mem_image.mpr ⟨_, LayerPacking.layerSupport_subset _ cols (List.get_mem cols _)
      (LayerPacking.sequenceCell_mem cols _ _), rfl⟩
  have hbridge : ∀ x, fwBridgeLayerCells rows cols hr hc x ∈ base := by
    rintro ⟨a, ⟨network, side⟩⟩
    cases network
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hrowmem _))
    · exact Finset.mem_union_right _ (hcolmem _)
  have hbridgefree : ∀ x, fwBridgeLayerCells rows cols hr hc x ∉ rect := by
    rintro ⟨a, ⟨network, side⟩⟩
    cases network
    · exact hrows.sequenceCell_unreserved _
    · intro hm
      exact (hcols.transposed_support_safe _ (hcolmem _)).1 (Finset.mem_union_left _ hm)
  have hprior : prior ⊆ base := by
    intro c hc'
    rcases Finset.mem_union.mp hc' with hd | ho
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨(bridgeDiagonalRectangle hrect x.1, x.2), Finset.mem_univ _, rfl⟩))
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ho
      exact hbridge x
  have hdiagfree : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      packedRectangleCorner hs choice (btGrowingOffsetRectangle (5 * (4 * 6)) hseed x.1, x.2) ∉ prior := by
    intro x hm
    rcases Finset.mem_union.mp hm with hd | ho
    · obtain ⟨y, _, heq⟩ := Finset.mem_image.mp hd
      have hl := congrArg Prod.fst ((packedRectangleCorner_injective hs choice) heq)
      have hn := fw_bridge_seed_rectangle_ne hrect hseed y.1 x.1
      apply hn
      apply Fin.ext
      simpa [btGrowingOffsetRectangle, fwSeedRectangle] using congrArg Fin.val hl
    · obtain ⟨y, _, heq⟩ := Finset.mem_image.mp ho
      apply hbridgefree y
      rw [heq]
      exact Finset.mem_image.mpr ⟨(btGrowingOffsetRectangle (5 * (4 * 6)) hseed x.1, x.2), Finset.mem_univ _, rfl⟩
  have hdisj : Disjoint (LayerPacking.layersSupport sr) (LayerPacking.transposeCells (LayerPacking.layersSupport sc)) := by
    apply Finset.disjoint_left.mpr
    intro c hsr' hsc'
    exact (hscols.transposed_support_safe c hsc').1 (Finset.mem_union_right _ hsr')
  have hgeom := btGrowingOffsetCells_geometry (P := 16) (d := 6) (r := 3)
    (5 * (4 * 6)) hseed hs choice base prior
    (by intro c hc'; exact Finset.mem_union_left _ (Finset.mem_union_left _ hc'))
    hprior hdiagfree sr sc hsr hsc hsrows hscols hdisj
  have hnot : ∀ c ∈ prior, c ∉ Set.range (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) := by
    intro c hc' ⟨x, hx⟩
    apply hgeom.2 ((Equiv.ofBijective (prefixPhysicalInput (P := 16)
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega)) (fwSeedPhysicalInput_bijective n)).symm x)
    change fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x ∈ prior
    rw [hx]
    exact hc'
  constructor
  · intro t side
    apply hfixed
    apply hnot
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(t,side), Finset.mem_univ _, rfl⟩)
  · intro x
    apply hfixed
    apply hnot
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)

end
end Sude
