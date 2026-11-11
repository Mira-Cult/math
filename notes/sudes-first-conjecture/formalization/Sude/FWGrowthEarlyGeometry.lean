import Sude.FWBridgeSeedCoverage
import Sude.FWWidePhysicalSlots

/-! Geometry of earlier FW role cells and offset growth rectangles. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- The actual bridge, retained-seed and wide role cells. -/
def fwGrowthEarlyRoleCells {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3) : Finset (Cell n) :=
  ((Finset.univ.image (fun x : Fin (5 * (4 * 6)) × Fin 4 =>
      packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect x.1, x.2)) ∪
    Finset.univ.image (fwBridgeLayerCells rows cols hr hc)) ∪
   (Finset.univ.image (fun x : Fin (16 * (4 * 6)) × Fin 4 =>
      packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) ∪
    Finset.univ.image (fwSeedOrdinaryCells sr sc hsr hsc))) ∪
   Finset.univ.image (fwWidePhysicalCells hwide hs choice wr wc hwr hwc)

/-- Geometric reservation including the full RP1 packing and six earlier layer families. -/
def fwGrowthEarlyBase {n L : ℕ} (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols sr sc wr wc : List (LayerPacking.Layer n)) : Finset (Cell n) :=
  (((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪
    LayerPacking.layersSupport sr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪
    LayerPacking.layersSupport wr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport wc)

/-- Rectangle labels for P growth stages follow all bridge, seed and wide labels. -/
def fwGrowthRectangle {n L P : ℕ}
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (t : Fin (P * (4 * 6))) : Fin L :=
  ⟨5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + t.val, by have h := t.isLt; omega⟩

theorem fwGrowthRectangle_injective {n L P : ℕ}
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L) :
    Function.Injective (fwGrowthRectangle hgrowth) := by
  intro x y h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [fwGrowthRectangle] at hv
  omega

/-- Every actual early role is inside the larger geometric reservation. -/
theorem fw_growth_early_roles_subset_base {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3) :
    fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc ⊆
      fwGrowthEarlyBase hs choice rows cols sr sc wr wc := by
  intro c hc'
  rcases Finset.mem_union.mp hc' with hearly | hwide'
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (fw_bridge_seed_role_images_subset_base hrect hseed hs choice rows cols hr hc sr sc hsr hsc hearly))
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hwide'
    cases x with
    | inl x =>
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨(fwWideRectangle hwide x.1, x.2), Finset.mem_univ _, rfl⟩
    | inr x =>
      rcases x with ⟨a, ⟨network, side⟩⟩
      cases network
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact LayerPacking.layerSupport_subset _ wr (List.get_mem wr _)
          (LayerPacking.sequenceCell_mem wr _ _)
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨_, LayerPacking.layerSupport_subset _ wc (List.get_mem wc _)
          (LayerPacking.sequenceCell_mem wc _ _), rfl⟩

/-- Growth rectangles lie outside the actual bridge, seed and wide roles.
Their corners remain in the full RP1 geometric reservation. -/
theorem fw_growth_corner_avoids_early_roles {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
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
    (wr wc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hwrows : LayerPacking.PackedLayers
      ((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport sc)) wr)
    (hwcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪ LayerPacking.layersSupport wr)) wc)
    (x : Fin (P * (4 * 6)) × Fin 4) :
    packedRectangleCorner hs choice (fwGrowthRectangle hgrowth x.1, x.2) ∉
      fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc := by
  let target := packedRectangleCorner hs choice (fwGrowthRectangle hgrowth x.1, x.2)
  let b0 := (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport sc)
  have htarget : target ∈ packedRectangleSupport hs choice :=
    Finset.mem_image.mpr ⟨(fwGrowthRectangle hgrowth x.1, x.2), Finset.mem_univ _, rfl⟩
  have htargetBase : target ∈ b0 :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ htarget)))
  have hbig : 5 * (4 * 6) + 16 * (4 * 6) + ((3 * (n / 450)) + P) * (4 * 6) ≤ L := by omega
  let wi : Fin (((3 * (n / 450)) + P) * (4 * 6)) :=
    ⟨(3 * (n / 450)) * (4 * 6) + x.1.val, by have h := x.1.isLt; omega⟩
  have heq : fwWideRectangle hbig wi = fwGrowthRectangle hgrowth x.1 := by
    apply Fin.ext
    simp [fwWideRectangle, fwGrowthRectangle, wi]
    omega
  have hprev := fw_wide_corner_avoids_bridge_seed_roles hrect hseed hbig hs choice
    rows cols hr hc hrows hcols sr sc hsr hsc hsrows hscols hsdisj (wi, x.2)
  rw [heq] at hprev
  have hrectbase : packedRectangleSupport hs choice ⊆ b0 := by
    intro c hc'
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hc')))
  have hsingleton : ({target} : Finset (Cell n)) ⊆ b0 := by
    intro c hc'
    simpa using (Finset.mem_singleton.mp hc') ▸ htargetBase
  have hdiagfree : ∀ z : Fin ((3 * (n / 450)) * (4 * 6)) × Fin 4,
      packedRectangleCorner hs choice (fwWideRectangle hwide z.1, z.2) ∉ ({target} : Finset (Cell n)) := by
    intro z hz
    have hcorner := Finset.mem_singleton.mp hz
    have hlabel := congrArg Prod.fst ((packedRectangleCorner_injective hs choice) hcorner)
    have hv := congrArg Fin.val hlabel
    simp only [fwWideRectangle, fwGrowthRectangle] at hv
    have hz' := z.1.isLt
    omega
  have hwdisj : Disjoint (LayerPacking.layersSupport wr) (LayerPacking.transposeCells (LayerPacking.layersSupport wc)) := by
    apply Finset.disjoint_left.mpr
    intro c hc' hd'
    exact (hwcols.transposed_support_safe c hd').1 (Finset.mem_union_right _ hc')
  have hwidefree := (fwWidePhysicalCells_geometry hwide hs choice b0 {target} hrectbase hsingleton
    hdiagfree wr wc hwr hwc hwrows hwcols hwdisj).2
  intro hrole
  rcases Finset.mem_union.mp hrole with hold | hw'
  · exact hprev hold
  · obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hw'
    apply hwidefree z
    apply Finset.mem_singleton.mpr
    exact hz

end
end Sude
