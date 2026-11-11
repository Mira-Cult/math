import Sude.FWFourFamilyLineCancellation
import Sude.FWReallocatedStageMeanSum
import Sude.FWSpareGlobalDeviationOfTheta
import Sude.FullReservationCancellationEnvelope

/-! Explicit reallocated-square scalar envelope for the four-family cancellation.
No full-line, concentration, diagonal or theta witness claim is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- Each row and column has its own actual incidence and an explicit scalar
cancellation envelope, with no active-role remainder. -/
theorem fw_reallocated_four_family_cancellation_envelope_of_theta
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
    let f := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
    let cells := f ∘ fwFourStageInputEquiv n P
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    let means := fun j : FWFourStageIndex n P =>
      (∑ i, (((entry new (cells ((j, i), false)) : ℝ) + entry new (cells ((j, i), true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let A : ℝ := ∑ j, (means j - μ)
    let D : ℝ := (∑ z ∈ full \ roles, (entry new z : ℝ)) - ((full \ roles).card : ℝ) * μ
    let N : ℝ := (n * n - (12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P)) : ℕ)
    let S := 5 + 16 + 3 * (n / 450) + P
    let Amax : ℝ := ((5 : ℝ) * (6109 / 231000) + ((16 + P : ℕ) : ℝ) * (257 / 500) +
      ((3 * (n / 450) : ℕ) : ℝ) / 235) * (poolMaximum n : ℝ)
    let Dmax : ℝ := (257 / 500 : ℝ) * (poolMaximum n : ℝ) * ((96 * (238 - P) : ℕ) : ℝ)
    let cancellation := fun q : ℕ =>
      let k : ℝ := (n - 12 * S - q : ℕ)
      2 * (6 : ℝ) * A + k * (centralEntriesMean (actualUnusedPool new full) centralPoolValue - μ) =
        (2 * (6 : ℝ) * A / N) * (((n : ℝ) + 8) * (q : ℝ) -
          96 * ((238 : ℝ) - P) - 8 * n) - k * D / N
    let envelope := fun q : ℕ =>
      |12 * A + ((n - 12 * S - q : ℕ) : ℝ) *
        (centralEntriesMean (actualUnusedPool new full) centralPoolValue - μ)| ≤
        (12 * Amax * (8 * (n : ℝ) + 96 * ((238 : ℝ) - P)) +
          ((n : ℝ) - ((12 * S : ℕ) : ℝ)) * Dmax) / N
    (∀ r : Fin n, ∃ q : ℕ, (q = 0 ∨ q = 2) ∧
      (LayerPacking.rowUsed full r).card = 12 * S + q ∧ 12 * S + q ≤ n ∧ cancellation q ∧ envelope q) ∧
    (∀ c : Fin n, ∃ q : ℕ, (q = 0 ∨ q = 2) ∧
      (LayerPacking.colUsed full c).card = 12 * S + q ∧ 12 * S + q ≤ n ∧ cancellation q ∧ envelope q) := by
  classical
  dsimp only
  let f := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  let cells := f ∘ fwFourStageInputEquiv n P
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
  let means := fun j : FWFourStageIndex n P =>
      (∑ i, (((entry new (cells ((j, i), false)) : ℝ) + entry new (cells ((j, i), true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ)
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
  let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  let A : ℝ := ∑ j, (means j - μ)
  let D : ℝ := (∑ z ∈ full \ roles, (entry new z : ℝ)) - ((full \ roles).card : ℝ) * μ
  let N : ℝ := (n * n - (12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P)) : ℕ)
  let S := 5 + 16 + 3 * (n / 450) + P
  let Amax : ℝ := ((5 : ℝ) * (6109 / 231000) + ((16 + P : ℕ) : ℝ) * (257 / 500) +
    ((3 * (n / 450) : ℕ) : ℝ) / 235) * (poolMaximum n : ℝ)
  let Dmax : ℝ := (257 / 500 : ℝ) * (poolMaximum n : ℝ) * ((96 * (238 - P) : ℕ) : ℝ)
  have hA : |A| ≤ Amax := by
    exact (fw_reallocated_four_family_stage_mean_sum_bound_of_theta bmor lower upper hnlo hnhi hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
      initial batches hvalid blocks hlen old new hdiag hord hplaced hmatched πb sb πw sw hbridge hwideEntry).2.2
  have hD : |D| ≤ Dmax := by
    exact fw_spare_global_deviation_of_theta bmor lower upper hnlo hnhi hP hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols new
  have hNnat : 0 < n * n - (12 * S * (n + 8) + 96 * (238 - P)) := by
    have hh := fw_full_reservation_card_formula_lt hnlo hP
    dsimp [S] at hh ⊢
    omega
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hNnat
  have hnReal : (19485 : ℝ) ≤ n := by exact_mod_cast hnlo
  have hPReal : (P : ℝ) ≤ 238 := by exact_mod_cast hP
  have hb : 0 ≤ 96 * ((238 : ℝ) - P) := by linarith
  have hcancel := fw_four_family_each_line_signed_cancellation hnlo hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols new
  dsimp only at hcancel
  have hbound (q : ℕ) (hq : q = 0 ∨ q = 2) (hline : 12 * S + q ≤ n)
      (hid : 12 * A + ((n - 12 * S - q : ℕ) : ℝ) *
          (centralEntriesMean (actualUnusedPool new full) centralPoolValue - μ) =
        (12 * A / N) * (((n : ℝ) + 8) * (q : ℝ) - 96 * ((238 : ℝ) - P) - 8 * n) -
          ((n - 12 * S - q : ℕ) : ℝ) * D / N) :
      |12 * A + ((n - 12 * S - q : ℕ) : ℝ) *
        (centralEntriesMean (actualUnusedPool new full) centralPoolValue - μ)| ≤
        (12 * Amax * (8 * (n : ℝ) + 96 * ((238 : ℝ) - P)) +
          ((n : ℝ) - ((12 * S : ℕ) : ℝ)) * Dmax) / N := by
    have hrq : 0 ≤ ((12 * S : ℕ) : ℝ) + (q : ℝ) ∧
        ((12 * S : ℕ) : ℝ) + (q : ℝ) ≤ (n : ℝ) := by
      constructor
      · positivity
      · exact_mod_cast hline
    have hqReal : (q : ℝ) = 0 ∨ (q : ℝ) = 2 := by
      rcases hq with hq | hq <;> simp [hq]
    have hk : ((n - 12 * S - q : ℕ) : ℝ) =
        (n : ℝ) - ((12 * S : ℕ) : ℝ) - (q : ℝ) := by
      rw [Nat.cast_sub (by omega : q ≤ n - 12 * S), Nat.cast_sub (by omega : 12 * S ≤ n)]
    rw [hk] at hid ⊢
    have h := full_reservation_cancellation_envelope (n : ℝ) ((12 * S : ℕ) : ℝ) (q : ℝ)
      (96 * ((238 : ℝ) - P)) N A 0 D
      (centralEntriesMean (actualUnusedPool new full) centralPoolValue) μ Amax 0 Dmax
      hnReal hb hN hrq hqReal ((abs_nonneg A).trans hA) (le_refl 0) ((abs_nonneg D).trans hD)
      hA (by simp) hD (by simpa only [zero_add] using hid)
    simpa only [zero_add] using h
  constructor
  · intro row
    obtain ⟨q, hq, hcount, hline, hid⟩ := hcancel.1 row
    have hid' := hid
    norm_num only at hid'
    exact ⟨q, hq, hcount, hline, hid, hbound q hq hline hid'⟩
  · intro col
    obtain ⟨q, hq, hcount, hline, hid⟩ := hcancel.2 col
    have hid' := hid
    norm_num only at hid'
    exact ⟨q, hq, hcount, hline, hid, hbound q hq hline hid'⟩

end
end Sude
