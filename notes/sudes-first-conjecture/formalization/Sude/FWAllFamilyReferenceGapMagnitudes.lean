import Sude.FWEarlyPairEndpointTransfer
import Sude.FWGrowthPairEndpointTransfer
import Sude.UnorderedPairInvariants

/-! Signed-gap magnitudes on a supplied fresh reference, conditional on
same-pair endpoint identity/reversal. This does not construct the reference,
fix signs, or claim any later flow output preserves these gaps. -/
namespace Sude
noncomputable section

/-- For any physical pair, identity or reversal preserves the magnitude of
an input nonnegative gap; its signed orientation may reverse. -/
theorem physical_pair_endpoint_gap_magnitude {n : ℕ}
    (a b : Cell n ≃ Fin (n*n)) (x y : Cell n) (g : ℕ)
    (hpair : pairEndpointSameOrSwapped a b x y)
    (hgap : entry a y = entry a x + g) :
    |(entry b y : ℤ) - entry b x| = (g : ℤ) := by
  exact unordered_pair_gap_magnitude (entry a x) (entry a y) (entry b x) (entry b y) g hpair hgap

/-- Retained seed, bridge, wide and growth physical pairs on the same fresh
reference have the original per-pair gap magnitudes under explicit input gap
and endpoint identity/reversal hypotheses. The bridge/wide gaps may vary
between blocks and growth gaps may vary between stages. -/
theorem fw_all_family_reference_gap_magnitudes {n L P : ℕ}
    (hrect : 5 * (4*6) ≤ L) (hseed : 5*(4*6) + 16*(4*6) ≤ L)
    (hwide : 5*(4*6) + 16*(4*6) + (3*(n/450))*(4*6) ≤ L)
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hr : br.length = 5*3) (hc : bc.length = 5*3)
    (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (hwr : wr.length = (3*(n/450))*3) (hwc : wc.length = (3*(n/450))*3)
    (hgr : gr.length = P*3) (hgc : gc.length = P*3)
    (a b : Cell n ≃ Fin (n*n))
    (gb : Fin 5 → Fin (3*(n+8)) → ℕ)
    (gw : Fin (3*(n/450)) → Fin (3*(n+8)) → ℕ)
    (gg : Fin P → ℕ)
    (hseedgap : ∀ j i, entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true)) =
      entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) + 2)
    (hbridgegap : ∀ j k p, entry a (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,k,p),true)) =
      entry a (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,k,p),false)) + gb j k)
    (hwidegap : ∀ j k p, entry a (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,k,p),true)) =
      entry a (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,k,p),false)) + gw j k)
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
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j i
    exact physical_pair_endpoint_gap_magnitude a b _ _ 2 (hseedpair j i) (hseedgap j i)
  · intro j k p
    exact physical_pair_endpoint_gap_magnitude a b _ _ (gb j k) (hbridgepair j k p) (hbridgegap j k p)
  · intro j k p
    exact physical_pair_endpoint_gap_magnitude a b _ _ (gw j k) (hwidepair j k p) (hwidegap j k p)
  · intro j i
    exact physical_pair_endpoint_gap_magnitude a b _ _ (gg j) (hgrowthpair j i) (hgrowthgap j i)

end
end Sude
