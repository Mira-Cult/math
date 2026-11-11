import Sude.FWProtectedDoubleBlockLogReallocation
import Sude.SeedConcentrationPreservation

/-! Reallocation restricted to the growth image preserves the other FW
families and their existing midpoint references. -/
namespace Sude
noncomputable section

/-- Fixing each physical double-block endpoint preserves the actual centered
score, retaining the original source square. -/
theorem double_block_actual_score_preserved {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (source before after : Cell n ≃ Fin (n*n))
    (hfixed : ∀ x, entry after (cells x) = entry before (cells x)) :
    doubleBlockActualCenteredScore cells line source after =
      doubleBlockActualCenteredScore cells line source before := by
  classical
  simp only [doubleBlockActualCenteredScore, doubleBlockPairMidpoint, hfixed]

/-- Under joint packing, changes confined to growth cells leave every seed,
bridge and wide endpoint fixed. Both centered scores retain the supplied
source square; this does not preserve any growth cell or network. -/
theorem fw_growth_reallocation_preserves_early_roles {n P : ℕ}
    (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
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
      (((bc ++ sc) ++ wc) ++ gc))
    (source before after : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c, c ∉ Set.range (btGrowingOffsetPairCells (Q := 6 * (n + 8))
      (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc) →
        entry after c = entry before c) :
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    (∀ x, entry after (seed x) = entry before (seed x)) ∧
    (∀ x, entry after (bridge x) = entry before (bridge x)) ∧
    (∀ x, entry after (wide x) = entry before (wide x)) ∧
    (∀ line : Cell n → Prop, doubleBlockActualCenteredScore bridge line source after =
      doubleBlockActualCenteredScore bridge line source before) ∧
    (∀ line : Cell n → Prop, doubleBlockActualCenteredScore wide line source after =
      doubleBlockActualCenteredScore wide line source before) := by
  classical
  dsimp only
  obtain ⟨_, _, _, _, hbg, _, hwg⟩ := fw_double_block_family_separation hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  obtain ⟨hall, _⟩ := fw_four_family_pair_cells_injective hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  have hsg : ∀ x y, fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x ≠
      btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc y := by
    intro x y he
    have he' := hall (show fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc (Sum.inl (Sum.inl (Sum.inr x))) =
      fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc (Sum.inr y) from he)
    simp only [reduceCtorEq] at he'
  have hsf : ∀ x, entry after (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x) =
      entry before (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x) := by
    intro x
    apply hfixed
    rintro ⟨y, hy⟩
    exact hsg x y hy.symm
  have hbf : ∀ x, entry after (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x) =
      entry before (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x) := by
    intro x
    apply hfixed
    rintro ⟨y, hy⟩
    exact hbg x y hy.symm
  have hwf : ∀ x, entry after (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x) =
      entry before (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x) := by
    intro x
    apply hfixed
    rintro ⟨y, hy⟩
    exact hwg x y hy.symm
  exact ⟨hsf, hbf, hwf,
    fun line => double_block_actual_score_preserved _ line source before after hbf,
    fun line => double_block_actual_score_preserved _ line source before after hwf⟩

end
end Sude
