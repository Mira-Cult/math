import Sude.FWBridgeWidePairPlacement
import Sude.FWMatchedBlockGeometry
import Sude.FWThetaInputs
import Sude.ReservedPoolMean
import Sude.FWPoolBound

/-! Wide pair midpoint bounds for the actual supplied physical placement.
No theta witness, stage-average, or line estimate is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- Every physical pair in the supplied matched blocks has the same midpoint bound. -/
theorem fw_wide_physical_pair_midpoint_bound {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (a : Cell n ≃ Fin (n * n))
    (hplaced : ∀ x : FWWideInputs n, entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (m X : ℝ) (hX : 100 ≤ X)
    (hmlo : (243 / 500 : ℝ) * X ≤ m) (hmhi : m ≤ (123 / 250 : ℝ) * X)
    (hvalid : ∀ b ∈ blocks, b.MatchedValid
      (bmorLowBins (fwReflectedLeft m X) (fwReflectedRight m X))
      (bmorHighBins (fwReflectedLeft m X) (fwReflectedRight m X)))
    (j : Fin (3 * (n / 450))) (i : Fin (6 * (n + 8))) :
    |(((entry a (fwWidePhysicalPairCells hwide hs choice rows cols hr hc ((j,i),false)) : ℝ) +
       (entry a (fwWidePhysicalPairCells hwide hs choice rows cols hr hc ((j,i),true)) : ℝ)) / 2) - m| ≤ X / 235 := by
  let kp : Fin (3 * (n + 8)) × Fin 2 := finProdFinEquiv.symm
    (Fin.cast (by omega : 6 * (n + 8) = 3 * (n + 8) * 2) i)
  have hi : Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8))
      (finProdFinEquiv kp) = i := by
    dsimp [kp]
    simp only [Equiv.apply_symm_apply, Fin.cast_cast, Fin.cast_refl, id_eq]
  let idx := Fin.cast hlen.symm (finProdFinEquiv (j, kp.1))
  let block := blocks.get idx
  have hb := fw_matched_block_pair_bounds m X hX hmlo hmhi block (hvalid block (List.get_mem blocks idx))
  have hfalse := fw_wide_pair_entry_oriented hwide hs choice rows cols hr hc blocks hlen a hplaced j kp.1 kp.2 false
  have htrue := fw_wide_pair_entry_oriented hwide hs choice rows cols hr hc blocks hlen a hplaced j kp.1 kp.2 true
  rw [show (kp.1, kp.2) = kp from Prod.eta kp, hi] at hfalse htrue
  rw [hfalse, htrue]
  have hn : |(((block.endpoint (prefixPairCorner kp.2 false) : ℕ) : ℝ) +
      (block.endpoint (prefixPairCorner kp.2 true) : ℝ)) / 2 - m| ≤ X / 235 := by
    have hp : kp.2 = 0 ∨ kp.2 = 1 := by
      have h := kp.2.isLt
      omega
    rcases hp with hp | hp
    · rw [hp]
      simpa [prefixPairCorner, DoublePair.endpoint] using hb.1
    · rw [hp]
      simpa [prefixPairCorner, DoublePair.endpoint] using hb.2.2.2.1
  simpa [doublePairSequenceEndpoint, block, idx] using hn

/-- The actual prescribed-pool mean and selected matched blocks give the
physical wide pair bound under explicit finite theta and RS assumptions. -/
theorem fw_wide_physical_pair_midpoint_bound_of_theta
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n L : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (a : Cell n ≃ Fin (n * n))
    (hplaced : ∀ x : FWWideInputs n, entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))))
    (j : Fin (3 * (n / 450))) (i : Fin (6 * (n + 8))) :
    |(((entry a (fwWidePhysicalPairCells hwide hs choice rows cols hr hc ((j,i),false)) : ℝ) +
       (entry a (fwWidePhysicalPairCells hwide hs choice rows cols hr hc ((j,i),true)) : ℝ)) / 2) -
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ (poolMaximum n : ℝ) / 235 := by
  have hXnat : 100 ≤ poolMaximum n := by
    have h := fw_poolMaximum_gt_four_seed lower hnlo
    omega
  have hX : (100 : ℝ) ≤ poolMaximum n := by exact_mod_cast hXnat
  obtain ⟨hlo, hhi⟩ := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo hnhi
  have hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤
      centralEntriesMean (prescribedPoolValues n) centralPoolValue := by
    rw [prescribedPoolValues_mean]
    exact hlo
  have hmhi : centralEntriesMean (prescribedPoolValues n) centralPoolValue ≤
      (123 / 250 : ℝ) * (poolMaximum n : ℝ) := by
    rw [prescribedPoolValues_mean]
    exact hhi
  exact fw_wide_physical_pair_midpoint_bound hwide hs choice rows cols hr hc blocks hlen a hplaced
    (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n)
    hX hmlo hmhi hmatched j i

end
end Sude
