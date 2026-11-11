import Sude.ActualUnusedKeepoutDifference
import Sude.FWRoleCellOccupancy

/-! Exact cardinal depletion from extra keepout cells. No claim is made
about the size, primality target suitability, or placement of those values. -/
namespace Sude
noncomputable section

/-- The extra cells' values are distinct and are all in the role-relative
unused pool; enlarging the reservation removes exactly those values. -/
theorem actualUnusedPool_extra_values_exact {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (roles full : Finset (Cell n))
    (hsub : roles ⊆ full) :
    (full \ roles).image (entryPool a) ⊆ actualUnusedPool a roles ∧
    actualUnusedPool a roles \ actualUnusedPool a full = (full \ roles).image (entryPool a) ∧
    ((full \ roles).image (entryPool a)).card = (full \ roles).card ∧
    ((full \ roles).image (entry a)).card = (full \ roles).card ∧
    (actualUnusedPool a roles).card = (actualUnusedPool a full).card + (full \ roles).card := by
  classical
  have heq := actualUnusedPool_full_eq_roles_sdiff a roles full hsub
  have hextra : (full \ roles).image (entryPool a) ⊆ actualUnusedPool a roles := by
    unfold actualUnusedPool
    apply Finset.image_subset_image
    intro c hc
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hc).2⟩
  have hremoved : actualUnusedPool a roles \ actualUnusedPool a full =
      (full \ roles).image (entryPool a) := by
    rw [heq]
    ext v
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨ha, hn⟩
      by_contra hv
      exact hn ⟨ha, hv⟩
    · intro hv
      exact ⟨hextra hv, fun h => h.2 hv⟩
  have hcardPool : ((full \ roles).image (entryPool a)).card = (full \ roles).card :=
    Finset.card_image_of_injective _ (entryPool a).injective
  have hcardNat : ((full \ roles).image (entry a)).card = (full \ roles).card :=
    Finset.card_image_of_injective _ (entry_injective a)
  have hcard := Finset.card_sdiff_add_card_eq_card hextra
  rw [← heq, hcardPool] at hcard
  exact ⟨hextra, hremoved, hcardPool, hcardNat, hcard.symm⟩

/-- Under the supplied FW stage bounds and normalized joint packing, the
additional full-reservation cells remove exactly `96 * (238 - P)` distinct
values from the role-relative unused pool. -/
theorem fw_actualUnusedPool_spare_role_card {n P : ℕ} (hP : P ≤ 238)
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
    (a : Cell n ≃ Fin (n * n)) :
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    roles ⊆ full ∧
    actualUnusedPool a roles \ actualUnusedPool a full = (full \ roles).image (entryPool a) ∧
    ((full \ roles).image (entry a)).card = 96 * (238 - P) ∧
    (actualUnusedPool a roles).card = (actualUnusedPool a full).card + 96 * (238 - P) := by
  dsimp only
  have hocc := fw_role_cell_occupancy hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  dsimp only at hocc
  have hextra := actualUnusedPool_extra_values_exact a _ _ hocc.1
  refine ⟨hocc.1, hextra.2.1, ?_, ?_⟩
  · rw [hextra.2.2.2.1, hocc.2.2.2.2.2.1]
  · rw [hextra.2.2.2.2, hocc.2.2.2.2.2.1]

end
end Sude
