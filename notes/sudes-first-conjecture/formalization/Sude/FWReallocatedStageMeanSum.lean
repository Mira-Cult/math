import Sude.FWReallocatedStageMeanBounds
import Sude.FWFourFamilyStageMeanSumOfTheta

/-! Four-family stage-mean scalar envelope on a supplied reallocated square.
No witness, line concentration, or full-line estimate is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

theorem fw_reallocated_four_family_stage_mean_sum_bound_of_theta
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n P L : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (old new : Cell n ≃ Fin (n * n))
    (hdiag : ∀ t side, entry old (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hord : ∀ x, entry old (fwBridgeLayerCells br bc hbr hbc x) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x))
    (hplaced : ∀ x : FWWideInputs n, entry old (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8)))) (sb : Fin 5 → Fin (3 * (n + 8)) → Bool)
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (sw : Fin (3 * (n / 450)) → Fin (3 * (n + 8)) → Bool)
    (hbridge : ∀ j b p side, entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,b,p),side)) =
      entry old (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,πb j b,doubleBlockPairSwap (sb j b) p),side)))
    (hwideEntry : ∀ j b p side, entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),side)) =
      entry old (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,πw j b,doubleBlockPairSwap (sw j b) p),side))) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let means := fun j : FWFourStageIndex n P =>
      (∑ i, (((entry new (cells ((j, i), false)) : ℝ) + entry new (cells ((j, i), true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ)
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    (∀ j : Fin 16, |means (Sum.inl (Sum.inl (Sum.inr j))) - μ| ≤
      (257 / 500 : ℝ) * (poolMaximum n : ℝ)) ∧
    (∀ j : Fin P, |means (Sum.inr j) - μ| ≤
      (257 / 500 : ℝ) * (poolMaximum n : ℝ)) ∧
    |∑ j, (means j - μ)| ≤
      ((5 : ℝ) * (6109 / 231000) + ((16 + P : ℕ) : ℝ) * (257 / 500) +
        ((3 * (n / 450) : ℕ) : ℝ) / 235) * (poolMaximum n : ℝ) := by
  classical
  dsimp only
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
  let means := fun j : FWFourStageIndex n P =>
    (∑ i, (((entry new (cells ((j, i), false)) : ℝ) + entry new (cells ((j, i), true))) / 2)) /
      ((6 * (n + 8) : ℕ) : ℝ)
  let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  have hb := fw_reallocated_bridge_wide_stage_means_bound_of_theta bmor lower upper hnlo hnhi
    hrect hseed hwide hoff hs choice br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
    initial batches hvalid blocks hlen old new hdiag hord hplaced hmatched πb sb πw sw hbridge hwideEntry
  have hc : ∀ j, |means j - μ| ≤ (257 / 500 : ℝ) * (poolMaximum n : ℝ) := by
    intro j
    exact fw_four_stage_mean_coarse_of_theta bmor lower upper hnlo hnhi (by omega) new cells j
  have hseed' : ∀ j : Fin 16, |means (Sum.inl (Sum.inl (Sum.inr j))) - μ| ≤
      (257 / 500 : ℝ) * (poolMaximum n : ℝ) := fun j => hc _
  have hgrowth' : ∀ j : Fin P, |means (Sum.inr j) - μ| ≤
      (257 / 500 : ℝ) * (poolMaximum n : ℝ) := fun j => hc _
  refine ⟨hseed', hgrowth', ?_⟩
  exact fw_four_family_sum_abs_bound (poolMaximum n : ℝ) (fun j => means j - μ)
    hb.1 hseed' hb.2 hgrowth'

end
end Sude
