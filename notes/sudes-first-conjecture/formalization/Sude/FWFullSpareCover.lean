import Sude.FWRoleCellOccupancy

namespace Sude
noncomputable section

/-- Charge every non-role value once, while retaining the supplied classification
of the actual role values on the same square. No band or stock claim is made. -/
theorem full_value_cover_from_roles_and_spares {n : ℕ}
    (a : Cell n ≃ Fin (n*n)) (full roles : Finset (Cell n))
    (ordinary wide : Finset ℕ) (D spare : ℕ)
    (hroles : roles.image (entry a) ⊆ ordinary ∪ wide)
    (hordinary : ordinary.card ≤ D) (hspare : (full \ roles).card ≤ spare) :
    full.image (entry a) ⊆ (ordinary ∪ (full \ roles).image (entry a)) ∪ wide ∧
    (ordinary ∪ (full \ roles).image (entry a)).card ≤ D + spare := by
  classical
  constructor
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    by_cases hzr : z ∈ roles
    · have h := hroles (Finset.mem_image.mpr ⟨z, hzr, rfl⟩)
      rcases Finset.mem_union.mp h with h | h
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h)))
      · exact Finset.mem_union.mpr (Or.inr h)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨z, Finset.mem_sdiff.mpr ⟨hz, hzr⟩, rfl⟩))))
  · calc
      _ ≤ ordinary.card + ((full \ roles).image (entry a)).card := Finset.card_union_le _ _
      _ ≤ ordinary.card + (full \ roles).card := Nat.add_le_add_left Finset.card_image_le _
      _ ≤ D + spare := Nat.add_le_add hordinary hspare

/-- The unused growth capacity pays for all spare rectangle corners.
This is only a capacity identity; the corresponding value bounds are separate. -/
theorem fw_prefix_spare_capacity_exact (n P : ℕ) (hP : P ≤ 238) :
    12 * (n + 8) * (16 + P) + 96 * (238 - P) +
      12 * n * (238 - P) = 12 * (n + 8) * 254 := by
  have hp : (238 - P) + P = 238 := by omega
  nlinarith

theorem fw_prefix_spare_capacity_le (n P : ℕ) (hP : P ≤ 238) :
    12 * (n + 8) * (16 + P) + 96 * (238 - P) ≤
      12 * (n + 8) * 254 := by
  have h := fw_prefix_spare_capacity_exact n P hP
  omega

/-- The separate five-stage bridge charge is included exactly once. -/
theorem fw_bridge_prefix_spare_capacity_le (n P : ℕ) (hP : P ≤ 238) :
    12 * (n + 8) * 5 + (12 * (n + 8) * (16 + P) + 96 * (238 - P)) ≤
      12 * (n + 8) * 5 + 12 * (n + 8) * 254 := by
  have h := fw_prefix_spare_capacity_le n P hP
  omega

/-- Full physical FW reservation, including all spare rectangles. -/
theorem fw_full_value_cover_from_roles_and_spares {n P : ℕ} (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice)
      (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (a : Cell n ≃ Fin (n*n)) (ordinary wide : Finset ℕ) (D : ℕ)
    (hordinary : ordinary.card ≤ D)
    (hroles : let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
      roles.image (entry a) ⊆ ordinary ∪ wide) :
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    full.image (entry a) ⊆ (ordinary ∪ (full \ roles).image (entry a)) ∪ wide ∧
    (ordinary ∪ (full \ roles).image (entry a)).card ≤ D + 96 * (238 - P) := by
  have hspare := (fw_role_cell_occupancy hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols).2.2.2.2.2.1
  exact full_value_cover_from_roles_and_spares a _ _ ordinary wide D _ hroles hordinary (le_of_eq hspare)

end
end Sude
