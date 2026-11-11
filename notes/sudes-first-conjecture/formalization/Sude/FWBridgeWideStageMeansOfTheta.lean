import Sude.FWFourFamilyStageTotals
import Sude.FWBridgePairMidpointOfTheta
import Sude.FWWidePairMidpointOfTheta

/-! Individual bridge and wide stage mean bounds on one supplied square.
No witness existence, sum-of-stages, concentration or line bound is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- A nonempty finite average inherits the uniform pointwise deviation. -/
theorem finite_uniform_mean_abs_deviation {Q : ℕ} (hQ : 0 < Q)
    (values : Fin Q → ℝ) (μ B : ℝ) (hvalues : ∀ i, |values i - μ| ≤ B) :
    |(∑ i, values i) / (Q : ℝ) - μ| ≤ B := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have ht : (∑ i : Fin Q, |values i - μ|) ≤ (Q : ℝ) * B := by
    calc
      _ ≤ ∑ _i : Fin Q, B := Finset.sum_le_sum (by intro i _; exact hvalues i)
      _ = _ := by simp
  have hs := (Finset.abs_sum_le_sum_abs (fun i : Fin Q => values i - μ) Finset.univ).trans ht
  have heq : (∑ i : Fin Q, values i) / (Q : ℝ) - μ =
      (∑ i : Fin Q, (values i - μ)) / (Q : ℝ) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  rw [heq, abs_div, abs_of_pos hQr, div_le_iff₀ hQr]
  nlinarith


/-- The actual four-family bridge and wide stage means inherit their pair
bounds, with the original nested stage labels and one prescribed-pool mean. -/
theorem fw_bridge_wide_stage_means_bound_of_theta
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
    (a : Cell n ≃ Fin (n * n))
    (hdiag : ∀ t side, entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hord : ∀ x, entry a (fwBridgeLayerCells br bc hbr hbc x) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x))
    (hplaced : ∀ x : FWWideInputs n, entry a (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n)))) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let means := fun j : FWFourStageIndex n P =>
      (∑ i, (((entry a (cells ((j, i), false)) : ℝ) + entry a (cells ((j, i), true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ)
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    (∀ j : Fin 5, |means (Sum.inl (Sum.inl (Sum.inl j))) - μ| ≤
      (6109 / 231000 : ℝ) * (poolMaximum n : ℝ)) ∧
    (∀ j : Fin (3 * (n / 450)), |means (Sum.inl (Sum.inr j)) - μ| ≤
      (poolMaximum n : ℝ) / 235) := by
  dsimp only
  constructor
  · intro j
    apply finite_uniform_mean_abs_deviation (show 0 < 6 * (n + 8) by omega)
    intro i
    exact fw_bridge_physical_pair_midpoint_bound_of_theta bmor lower upper hnlo hnhi
      hrect hs choice br bc hbr hbc initial batches hvalid a hdiag hord j i
  · intro j
    apply finite_uniform_mean_abs_deviation (show 0 < 6 * (n + 8) by omega)
    intro i
    exact fw_wide_physical_pair_midpoint_bound_of_theta bmor lower upper hnlo hnhi
      hwide hs choice wr wc hwr hwc blocks hlen a hplaced hmatched j i

end
end Sude
