import Sude.FWBridgeWidePairCells
import Sude.BTGrowingPhysicalStageTotals
import Sude.FWSeedExistingReallocation

/-! The four physical pair maps cover exactly the supplied FW active roles.
This is reindexing only, without physical injectivity or value assumptions. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768

/-- The retained-seed pair map covers exactly its rectangle and layer roles. -/
theorem fw_seed_existing_pair_cells_image {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) :
    Finset.univ.image (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) =
      Finset.univ.image (fun x : Fin (16 * (4 * 6)) × Fin 4 =>
        packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) ∪
      Finset.univ.image (fwSeedOrdinaryCells sr sc hsr hsc) := by
  classical
  let e := Equiv.ofBijective (prefixPhysicalInput (P := 16)
    (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
    (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega)) (fwSeedPhysicalInput_bijective n)
  change Finset.univ.image ((btGrowingOffsetCells (5 * (4 * 6)) hseed hs choice sr sc hsr hsc) ∘ e.symm) = _
  rw [← Finset.image_image, Finset.image_univ_of_surjective e.symm.surjective]
  ext c
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨x, hx⟩
    cases x with
    | inl x => exact Or.inl ⟨x, hx⟩
    | inr x => exact Or.inr ⟨x, by cases x <;> exact hx⟩
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr x, by cases x <;> exact hx⟩

/-- The growth pair map has the same image as the supplied growth role map. -/
theorem bt_growing_offset_pair_cells_image {P d r n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (r * n) = Q)
    (offset : ℕ) (hoff : offset + P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P * r) (hc : cols.length = P * r) :
    Finset.univ.image (btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc) =
      Finset.univ.image (btGrowingOffsetCells offset hoff hs choice rows cols hr hc) := by
  classical
  change Finset.univ.image ((btGrowingOffsetCells offset hoff hs choice rows cols hr hc) ∘
    (prefixPhysicalInputEquiv hfit hdiag hexact).symm) = _
  rw [← Finset.image_image, Finset.image_univ_of_surjective (prefixPhysicalInputEquiv hfit hdiag hexact).symm.surjective]

/-- All four physical pair maps cover the actual FW active roles at the
canonical growth offset, without assuming that any two cells are distinct. -/
theorem fw_four_family_pair_cells_cover_roles {n P L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3) :
    let offset := 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)
    let bridge := fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let wide := fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    ((Finset.univ.image bridge ∪ Finset.univ.image seed) ∪ Finset.univ.image wide) ∪
      Finset.univ.image growth =
    fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc) := by
  classical
  dsimp only
  rw [fw_bridge_physical_pair_cells_image, fw_seed_existing_pair_cells_image,
    fw_wide_physical_pair_cells_image, bt_growing_offset_pair_cells_image]
  rfl

end
end Sude
