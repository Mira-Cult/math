import Sude.FWAllFamilyReferenceGapMagnitudes

/-! Transfer early-family gap equations through pointwise fixed cells to the
same ordered final square, then derive four-family gap magnitudes on the
supplied fresh reference. Nothing is asserted for later flow outputs. -/
namespace Sude
noncomputable section

theorem fw_fixed_early_reference_gap_magnitudes {n L P : ℕ}
    (hrect : 5 * (4*6) ≤ L) (hseed : 5*(4*6) + 16*(4*6) ≤ L)
    (hwide : 5*(4*6) + 16*(4*6) + (3*(n/450))*(4*6) ≤ L)
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hr : br.length = 5*3) (hc : bc.length = 5*3)
    (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (hwr : wr.length = (3*(n/450))*3) (hwc : wc.length = (3*(n/450))*3)
    (hgr : gr.length = P*3) (hgc : gc.length = P*3)
    (new a b : Cell n ≃ Fin (n*n))
    (gb : Fin 5 → Fin (3*(n+8)) → ℕ)
    (gw : Fin (3*(n/450)) → Fin (3*(n+8)) → ℕ)
    (gg : Fin P → ℕ)
    (hsf : ∀ x, entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x) =
      entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x))
    (hbf : ∀ x, entry a (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc x) =
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc x))
    (hwf : ∀ x, entry a (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x))
    (hseedgap : ∀ j i, entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true)) =
      entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) + 2)
    (hbridgegap : ∀ j k p, entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,k,p),true)) =
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,k,p),false)) + gb j k)
    (hwidegap : ∀ j k p, entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,k,p),true)) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,k,p),false)) + gw j k)
    (hgrowthgap : ∀ j i, entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice gr gc hgr hgc ((j,i),true)) =
      entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice gr gc hgr hgc ((j,i),false)) + gg j)
    (hseedpair : ∀ j i, pairEndpointSameOrSwapped a b
      (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false))
      (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true)))
    (hbridgepair : ∀ j k p, pairEndpointSameOrSwapped a b
      (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,k,p),false))
      (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,k,p),true)))
    (hwidepair : ∀ j k p, pairEndpointSameOrSwapped a b
      (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,k,p),false))
      (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,k,p),true)))
    (hgrowthpair : ∀ j i, pairEndpointSameOrSwapped a b
      (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice gr gc hgr hgc ((j,i),false))
      (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice gr gc hgr hgc ((j,i),true))) :
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    (∀ j i, |(entry b (seed ((j,i),true)) : ℤ) - entry b (seed ((j,i),false))| = 2) ∧
    (∀ j k p, |(entry b (bridge ((j,k,p),true)) : ℤ) - entry b (bridge ((j,k,p),false))| = (gb j k : ℤ)) ∧
    (∀ j k p, |(entry b (wide ((j,k,p),true)) : ℤ) - entry b (wide ((j,k,p),false))| = (gw j k : ℤ)) ∧
    (∀ j i, |(entry b (growth ((j,i),true)) : ℤ) - entry b (growth ((j,i),false))| = (gg j : ℤ)) := by
  apply fw_all_family_reference_gap_magnitudes hrect hseed hwide offset hoff hs choice
    br bc sr sc wr wc gr gc hr hc hsr hsc hwr hwc hgr hgc a b gb gw gg
  · intro j i
    rw [hsf ((j,i),true), hsf ((j,i),false)]
    exact hseedgap j i
  · intro j k p
    rw [hbf ((j,k,p),true), hbf ((j,k,p),false)]
    exact hbridgegap j k p
  · intro j k p
    rw [hwf ((j,k,p),true), hwf ((j,k,p),false)]
    exact hwidegap j k p
  · exact hgrowthgap
  · exact hseedpair
  · exact hbridgepair
  · exact hwidepair
  · exact hgrowthpair

end
end Sude
