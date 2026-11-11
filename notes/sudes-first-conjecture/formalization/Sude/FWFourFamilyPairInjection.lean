import Sude.FWFourFamilyRoleCoverage
import Sude.FWRoleCellOccupancy

/-! All FW pair roles are distinct under the supplied normalized packing.
No value, theta witness, mean or line bound is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- Domain of bridge, seed, wide and growth pair endpoints, in that order. -/
abbrev FWFourFamilyPairInputs (n P : ℕ) :=
  ((((Fin 5 × Fin (6 * (n + 8))) × Bool) ⊕
    ((Fin 16 × Fin (6 * (n + 8))) × Bool)) ⊕
    ((Fin (3 * (n / 450)) × Fin (6 * (n + 8))) × Bool)) ⊕
    ((Fin P × Fin (6 * (n + 8))) × Bool)

/-- The four same-geometry physical pair maps as one map. -/
def fwFourFamilyPairCells {n P L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3) : FWFourFamilyPairInputs n P → Cell n :=
  Sum.elim (Sum.elim (Sum.elim (fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc)
    (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc))
    (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc))
    (btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)

private theorem image_sum_univ {α β γ : Type*} [Fintype α] [Fintype β]
    [DecidableEq γ] (f : α → γ) (g : β → γ) :
    Finset.univ.image (Sum.elim f g) = Finset.univ.image f ∪ Finset.univ.image g := by
  classical
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨x, hx⟩
    cases x with
    | inl a => exact Or.inl ⟨a, hx⟩
    | inr b => exact Or.inr ⟨b, hx⟩
  · rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    · exact ⟨Sum.inl a, ha⟩
    · exact ⟨Sum.inr b, hb⟩

/-- The combined pair map is injective and covers precisely the active roles. -/
theorem fw_four_family_pair_cells_injective {n P : ℕ}
    (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc)) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    Function.Injective cells ∧ Finset.univ.image cells = roles := by
  classical
  dsimp only
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
  have himage : Finset.univ.image cells = roles := by
    dsimp [cells, fwFourFamilyPairCells]
    rw [image_sum_univ, image_sum_univ, image_sum_univ]
    exact fw_four_family_pair_cells_cover_roles hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  have hrole : roles.card = 12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) := by
    exact (fw_role_cell_occupancy hP hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols).2.1
  have hdomain : Fintype.card (FWFourFamilyPairInputs n P) =
      12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) := by
    simp only [FWFourFamilyPairInputs, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool]
    ring
  have hcard : (Finset.univ.image cells).card = (Finset.univ : Finset (FWFourFamilyPairInputs n P)).card := by
    rw [himage, hrole, Finset.card_univ, hdomain]
  have hinj : Function.Injective cells := by
    intro x y hxy
    exact (Finset.card_image_iff.mp hcard) (Finset.mem_univ x) (Finset.mem_univ y) hxy
  exact ⟨hinj, himage⟩

end
end Sude
