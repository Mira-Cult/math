import Sude.FWBridgeWideDoubleReallocation

/-! Injectivity and physical disjointness of the grouped bridge and wide
families under the same supplied normalized joint packing. -/
namespace Sude
noncomputable section

/-- The actual grouped bridge and wide families are individually injective
and have disjoint physical-cell images. -/
theorem fw_grouped_bridge_wide_geometry {n P : ℕ}
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
      (((bc ++ sc) ++ wc) ++ gc)) :
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    Function.Injective bridge ∧ Function.Injective wide ∧
      Disjoint (Finset.univ.image bridge) (Finset.univ.image wide) := by
  classical
  dsimp only
  obtain ⟨hfamily, _⟩ := fw_four_family_pair_cells_injective hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  change Function.Injective cells at hfamily
  have hb : Function.Injective (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n x)))) =
        cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n y)))) from h)
    exact (fwBlockPairIndex 5 n).injective (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj he)))
  have hw : Function.Injective (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n x))) =
        cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n y))) from h)
    exact (fwBlockPairIndex (3 * (n / 450)) n).injective (Sum.inr.inj (Sum.inl.inj he))
  refine ⟨hb, hw, ?_⟩
  apply Finset.disjoint_left.mpr
  intro z hz₁ hz₂
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz₁
  obtain ⟨y, _, heq⟩ := Finset.mem_image.mp hz₂
  have he := hfamily (show cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n x)))) =
    cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n y))) from heq.symm)
  simp only [Sum.inl.injEq, reduceCtorEq] at he

end
end Sude
