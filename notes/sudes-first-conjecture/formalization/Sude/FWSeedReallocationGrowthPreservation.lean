import Sude.FWSeedExistingReallocation

/-! Preservation of supplied growth roles when only the already-installed seed
cells are reallocated. The caller supplies the growth packing and the actual
early-reservation separation; no diagonal-sum or flow claim is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- Every cell that can be changed by seed reallocation is an actual early role. -/
theorem fw_seed_existing_cells_mem_early {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (x : (Fin 16 × Fin (6 * (n + 8))) × Bool) :
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x ∈
      fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc := by
  classical
  unfold fwSeedExistingPairCells
  generalize ((Equiv.ofBijective _ _).symm x) = y
  cases y with
  | inl y =>
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
  | inr y =>
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, by cases y <;> rfl⟩

/-- An entry equality outside the seed image applies to every cell outside the
actual early roles, without assuming anything about how either square was made. -/
theorem fw_seed_reallocation_preserves_outside_early {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (grown b : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c, c ∉ Set.range (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) →
      entry b c = entry grown c)
    (c : Cell n)
    (hfree : c ∉ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc) :
    entry b c = entry grown c := by
  apply hfixed
  rintro ⟨x, rfl⟩
  exact hfree (fw_seed_existing_cells_mem_early hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc x)

/-- All growth-role entries are retained when their offset geometry avoids the
actual early reservation and the two growth layer families are packed after it.
The corner-avoidance input follows from `fw_growth_corner_avoids_early_roles`
under its stated geometric packing hypotheses. -/
theorem fw_seed_reallocation_preserves_growth_roles {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hgrpacked : LayerPacking.PackedLayers (fwGrowthEarlyBase hs choice rows cols sr sc wr wc) gr)
    (hgcpacked : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (fwGrowthEarlyBase hs choice rows cols sr sc wr wc ∪ LayerPacking.layersSupport gr)) gc)
    (hgdisj : Disjoint (LayerPacking.layersSupport gr) (LayerPacking.transposeCells (LayerPacking.layersSupport gc)))
    (hdiagfree : ∀ x : Fin (P * (4 * 6)) × Fin 4,
      packedRectangleCorner hs choice (btGrowingOffsetRectangle
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hgrowth x.1, x.2) ∉
        fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc)
    (grown b : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c, c ∉ Set.range (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) →
      entry b c = entry grown c) :
    ∀ x : PrefixPhysicalInputs P 6 3 n,
      entry b (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hgrowth hs choice gr gc hgr hgc x) =
      entry grown (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hgrowth hs choice gr gc hgr hgc x) := by
  let base := fwGrowthEarlyBase hs choice rows cols sr sc wr wc
  let prior := fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc
  have hrectbase : packedRectangleSupport hs choice ⊆ base := by
    intro c hc'
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hc')))))
  have hprior : prior ⊆ base := fw_growth_early_roles_subset_base hrect hseed hwide hs choice
    rows cols hr hc sr sc hsr hsc wr wc hwr hwc
  have hfree := (btGrowingOffsetCells_geometry
    (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hgrowth hs choice
    base prior hrectbase hprior hdiagfree gr gc hgr hgc hgrpacked hgcpacked hgdisj).2
  intro x
  exact fw_seed_reallocation_preserves_outside_early hrect hseed hwide hs choice
    rows cols hr hc sr sc hsr hsc wr wc hwr hwc grown b hfixed _ (hfree x)

end
end Sude
