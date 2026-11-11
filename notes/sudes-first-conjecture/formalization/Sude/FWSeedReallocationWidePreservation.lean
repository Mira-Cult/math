import Sude.FWSeedExistingReallocation

/-! Preservation of supplied wide-role entries when the already-installed seed
cells are reallocated. No diagonal-sum, flow, or reconstruction claim is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- Every seed reallocation cell is in the actual bridge-and-seed role image. -/
theorem fw_seed_existing_cells_mem_bridge_seed_roles {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (x : (Fin 16 × Fin (6 * (n + 8))) × Bool) :
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x ∈
      (Finset.univ.image (fun y : Fin (5 * (4 * 6)) × Fin 4 =>
        packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect y.1, y.2)) ∪
       Finset.univ.image (fwBridgeLayerCells rows cols hr hc)) ∪
      (Finset.univ.image (fun y : Fin (16 * (4 * 6)) × Fin 4 =>
        packedRectangleCorner hs choice (fwSeedRectangle hseed y.1, y.2)) ∪
       Finset.univ.image (fwSeedOrdinaryCells sr sc hsr hsc)) := by
  classical
  unfold fwSeedExistingPairCells
  generalize ((Equiv.ofBijective _ _).symm x) = y
  apply Finset.mem_union_right
  cases y with
  | inl y =>
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
  | inr y =>
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, by cases y <;> rfl⟩

/-- Wide-role entries survive any change confined to the already-installed seed
image, provided the actual wide layout is packed after the bridge and seed
roles and its rectangle corners avoid those roles. -/
theorem fw_seed_reallocation_preserves_wide_roles {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (hwrpacked : LayerPacking.PackedLayers
      ((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport sc)) wr)
    (hwcpacked : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪ LayerPacking.layersSupport wr)) wc)
    (hwdisj : Disjoint (LayerPacking.layersSupport wr) (LayerPacking.transposeCells (LayerPacking.layersSupport wc)))
    (hdiagfree : ∀ x : Fin ((3 * (n / 450)) * (4 * 6)) × Fin 4,
      packedRectangleCorner hs choice (fwWideRectangle hwide x.1, x.2) ∉
      (Finset.univ.image (fun y : Fin (5 * (4 * 6)) × Fin 4 =>
        packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect y.1, y.2)) ∪
       Finset.univ.image (fwBridgeLayerCells rows cols hr hc)) ∪
      (Finset.univ.image (fun y : Fin (16 * (4 * 6)) × Fin 4 =>
        packedRectangleCorner hs choice (fwSeedRectangle hseed y.1, y.2)) ∪
       Finset.univ.image (fwSeedOrdinaryCells sr sc hsr hsc)))
    (grown b : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c, c ∉ Set.range (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) →
      entry b c = entry grown c) :
    ∀ x : FWWideInputs n,
      entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) := by
  let base := (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport sc)
  let prior := (Finset.univ.image (fun y : Fin (5 * (4 * 6)) × Fin 4 =>
    packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect y.1, y.2)) ∪
    Finset.univ.image (fwBridgeLayerCells rows cols hr hc)) ∪
    (Finset.univ.image (fun y : Fin (16 * (4 * 6)) × Fin 4 =>
    packedRectangleCorner hs choice (fwSeedRectangle hseed y.1, y.2)) ∪
    Finset.univ.image (fwSeedOrdinaryCells sr sc hsr hsc))
  have hrectbase : packedRectangleSupport hs choice ⊆ base := by
    intro c h
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  have hprior : prior ⊆ base := fw_bridge_seed_role_images_subset_base hrect hseed hs choice
    rows cols hr hc sr sc hsr hsc
  have hfree := (fwWidePhysicalCells_geometry hwide hs choice base prior hrectbase hprior
    hdiagfree wr wc hwr hwc hwrpacked hwcpacked hwdisj).2
  intro x
  apply hfixed
  rintro ⟨y, hy⟩
  apply hfree x
  rw [← hy]
  exact fw_seed_existing_cells_mem_bridge_seed_roles hrect hseed hs choice
    rows cols hr hc sr sc hsr hsc y

end
end Sude
