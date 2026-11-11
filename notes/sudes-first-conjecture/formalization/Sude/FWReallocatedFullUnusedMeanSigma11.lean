import Sude.FWReallocatedFullUnusedMean
import Sude.FWFullReservationQuarterCapacity

/-! First-band full-unused mean bound for a supplied reallocated witness.
No witness existence or CY gate is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

private theorem scratch_fw_first_band_sharp_sigma_11_100 {n P : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hP : P ≤ 238) :
    let Q : ℝ := 12*((n : ℝ)+8)*((5 : ℝ)*(6109/231000) +
      ((16+P : ℕ) : ℝ)*(257/500) + ((3*(n/450) : ℕ) : ℝ)/235) +
      (257/500 : ℝ)*((96*(238-P) : ℕ) : ℝ)
    let N : ℝ := ((n*n - (12*(5+16+3*(n/450)+P)*(n+8) + 96*(238-P)) : ℕ) : ℝ)
    0 < N ∧ Q ≤ (11/100)*N := by
  dsimp only
  have hquarter := fw_full_reservation_formula_quarter hnlo hP
  have hless := fw_full_reservation_card_formula_lt hnlo hP
  have hn : (19485 : ℝ) ≤ n := by exact_mod_cast hnlo
  have hp : (P : ℝ) ≤ 238 := by exact_mod_cast hP
  have hdiv : n/450 ≤ 79 := by omega
  have hd : ((n/450 : ℕ) : ℝ) ≤ 79 := by exact_mod_cast hdiv
  have hsp : ((238-P : ℕ) : ℝ) ≤ 238 := by exact_mod_cast (Nat.sub_le 238 P)
  have hN : ((n*n - (12*(5+16+3*(n/450)+P)*(n+8) + 96*(238-P)) : ℕ) : ℝ) =
      (n : ℝ)^2 - ((12*(5+16+3*(n/450)+P)*(n+8) + 96*(238-P) : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hquarterR : (4:ℝ) * ((12*(5+16+3*(n/450)+P)*(n+8) + 96*(238-P) : ℕ) : ℝ) ≤ (n : ℝ)^2 := by
    have h : (4:ℝ) * ((12*(5+16+3*(n/450)+P)*(n+8) + 96*(238-P) : ℕ) : ℝ) ≤ (n : ℝ)*(n : ℝ) := by exact_mod_cast hquarter
    simpa [pow_two] using h
  have hNlo : (3:ℝ)*(n : ℝ)^2 ≤ 4 * ((n*n - (12*(5+16+3*(n/450)+P)*(n+8) + 96*(238-P)) : ℕ) : ℝ) := by
    rw [hN]
    nlinarith
  have hC : (5 : ℝ)*(6109/231000) + ((16+P : ℕ) : ℝ)*(257/500) + ((3*(n/450) : ℕ) : ℝ)/235 ≤ 132 := by
    push_cast
    nlinarith
  have hsp' : (257/500 : ℝ)*((96*(238-P) : ℕ) : ℝ) ≤ 11800 := by
    push_cast
    nlinarith
  have hQ : 12*((n : ℝ)+8)*((5 : ℝ)*(6109/231000) + ((16+P : ℕ) : ℝ)*(257/500) + ((3*(n/450) : ℕ) : ℝ)/235) + (257/500 : ℝ)*((96*(238-P) : ℕ) : ℝ) ≤ 12*((n : ℝ)+8)*132 + 11800 := by
    nlinarith
  have hsquare : 19485*(n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  constructor
  · rw [hN]
    nlinarith
  · nlinarith
private theorem scratch_scaled_numerator_to_mean_11_100
    (K C D X N value : ℝ) (hX : 0 ≤ X) (hN : 0 < N)
    (hQ : K*C+D ≤ (11/100)*N)
    (hmean : |value| ≤ (K*(C*X)+D*X)/N) :
    |value| ≤ (11/100)*X := by
  apply hmean.trans
  have hm := mul_le_mul_of_nonneg_right hQ hX
  apply (div_le_iff₀ hN).2
  nlinarith


theorem fw_reallocated_full_unused_mean_11_100_of_theta
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n P : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hP : P ≤ 238)
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
      (((bc ++ sc) ++ wc) ++ gc))
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
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    |centralEntriesMean (actualUnusedPool new full) centralPoolValue - μ| ≤
      (11 / 100 : ℝ) * (poolMaximum n : ℝ) := by
  classical
  dsimp only
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
  let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  let N : ℝ := (n * n - (12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P)) : ℕ)
  have hbound := fw_reallocated_full_unused_mean_bound_of_theta bmor lower upper hnlo (by omega : n ≤ 35733)
    hP hrect hseed hwide hoff hs choice br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
    initial batches hvalid blocks hlen old new hdiag hord hplaced hmatched πb sb πw sw hbridge hwideEntry
  dsimp only at hbound
  have hnum := scratch_fw_first_band_sharp_sigma_11_100 hnlo hnhi hP
  dsimp only at hnum
  have hscaled := scratch_scaled_numerator_to_mean_11_100
    (12*((n : ℝ)+8))
    ((5 : ℝ)*(6109/231000) + ((16+P : ℕ) : ℝ)*(257/500) + ((3*(n/450) : ℕ) : ℝ)/235)
    ((257/500 : ℝ)*((96*(238-P) : ℕ) : ℝ))
    (poolMaximum n : ℝ) N
    (centralEntriesMean (actualUnusedPool new full) centralPoolValue - μ)
    (by positivity) hnum.1 hnum.2
  apply hscaled
  simpa only [full, μ, N, mul_assoc, mul_left_comm, mul_comm] using hbound

end
end Sude

