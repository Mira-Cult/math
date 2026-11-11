import Sude.FWFourFamilyLineEnvelopeOfTheta
import Sude.FWScalarAllStagesFirstBandGate

/-! First-band scalar cancellation for the supplied physical square. This is
not a full-line, theta witness, concentration, or diagonal bound. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

theorem fw_scalar_physical_envelope_identity (n P : ℕ) (hnlo : 19485 ≤ n) (hP : P ≤ 238) (X : ℝ) :
    let S := 5 + 16 + 3 * (n / 450) + P
    let Amax : ℝ := ((5 : ℝ) * (6109 / 231000) + ((16 + P : ℕ) : ℝ) * (257 / 500) +
      ((3 * (n / 450) : ℕ) : ℝ) / 235) * X
    let Dmax : ℝ := (257 / 500 : ℝ) * X * ((96 * (238 - P) : ℕ) : ℝ)
    let N : ℝ := (n * n - (12 * S * (n + 8) + 96 * (238 - P)) : ℕ)
    (12 * Amax * (8 * (n : ℝ) + 96 * ((238 : ℝ) - P)) +
      ((n : ℝ) - ((12 * S : ℕ) : ℝ)) * Dmax) / N =
      X * (fwScalarEnvelopeT n ((n / 450 : ℕ) : ℝ) P / fwScalarEnvelopeN n ((n / 450 : ℕ) : ℝ) P) := by
  dsimp only
  have hreserve : 12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P) ≤ n * n :=
    (fw_full_reservation_card_formula_lt hnlo hP).le
  have hN : ((n * n - (12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P)) : ℕ) : ℝ) =
      fwScalarEnvelopeN n ((n / 450 : ℕ) : ℝ) P := by
    rw [Nat.cast_sub hreserve]
    push_cast [Nat.cast_sub hP]
    dsimp [fwScalarEnvelopeN, fwScalarEnvelopeR, fwScalarEnvelopeB]
    ring
  have hnum : (12 * (((5 : ℝ) * (6109 / 231000) + ((16 + P : ℕ) : ℝ) * (257 / 500) +
      ((3 * (n / 450) : ℕ) : ℝ) / 235) * X) * (8 * (n : ℝ) + 96 * ((238 : ℝ) - P)) +
      ((n : ℝ) - ((12 * (5 + 16 + 3 * (n / 450) + P) : ℕ) : ℝ)) *
        ((257 / 500 : ℝ) * X * ((96 * (238 - P) : ℕ) : ℝ))) =
      X * fwScalarEnvelopeT n ((n / 450 : ℕ) : ℝ) P := by
    push_cast [Nat.cast_sub hP]
    dsimp [fwScalarEnvelopeT, fwScalarEnvelopeA, fwScalarEnvelopeR, fwScalarEnvelopeB]
    ring
  rw [hN, hnum]
  ring

/-- Each same-square first-band cancellation satisfies the strict scalar gate. -/
theorem fw_first_band_physical_cancellation_gate
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
    let f := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
    let cells := f ∘ fwFourStageInputEquiv n P
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    let means := fun j : FWFourStageIndex n P =>
      (∑ i, (((entry a (cells ((j, i), false)) : ℝ) + entry a (cells ((j, i), true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let A : ℝ := ∑ j, (means j - μ)
    let D : ℝ := (∑ z ∈ full \ roles, (entry a z : ℝ)) - ((full \ roles).card : ℝ) * μ
    let N : ℝ := (n * n - (12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P)) : ℕ)
    let S := 5 + 16 + 3 * (n / 450) + P
    let cancellation := fun q : ℕ =>
      let k : ℝ := (n - 12 * S - q : ℕ)
      2 * (6 : ℝ) * A + k * (centralEntriesMean (actualUnusedPool a full) centralPoolValue - μ) =
        (2 * (6 : ℝ) * A / N) * (((n : ℝ) + 8) * (q : ℝ) -
          96 * ((238 : ℝ) - P) - 8 * n) - k * D / N
    let bound := fun q : ℕ =>
      |12 * A + ((n - 12 * S - q : ℕ) : ℝ) *
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue - μ)| <
        (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * (poolMaximum n : ℝ)
    (∀ r : Fin n, ∃ q : ℕ, (q = 0 ∨ q = 2) ∧
      (LayerPacking.rowUsed full r).card = 12 * S + q ∧ 12 * S + q ≤ n ∧ cancellation q ∧ bound q) ∧
    (∀ c : Fin n, ∃ q : ℕ, (q = 0 ∨ q = 2) ∧
      (LayerPacking.colUsed full c).card = 12 * S + q ∧ 12 * S + q ≤ n ∧ cancellation q ∧ bound q) := by
  classical
  dsimp only
  let f := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  let cells := f ∘ fwFourStageInputEquiv n P
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
  let means := fun j : FWFourStageIndex n P =>
      (∑ i, (((entry a (cells ((j, i), false)) : ℝ) + entry a (cells ((j, i), true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ)
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
  let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  let A : ℝ := ∑ j, (means j - μ)
  let D : ℝ := (∑ z ∈ full \ roles, (entry a z : ℝ)) - ((full \ roles).card : ℝ) * μ
  let N : ℝ := (n * n - (12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P)) : ℕ)
  let S := 5 + 16 + 3 * (n / 450) + P
  let Amax : ℝ := ((5 : ℝ) * (6109 / 231000) + ((16 + P : ℕ) : ℝ) * (257 / 500) +
    ((3 * (n / 450) : ℕ) : ℝ) / 235) * (poolMaximum n : ℝ)
  let Dmax : ℝ := (257 / 500 : ℝ) * (poolMaximum n : ℝ) * ((96 * (238 - P) : ℕ) : ℝ)
  have hphys := fw_four_family_each_line_cancellation_envelope_of_theta bmor lower upper hnlo (by omega) hP
    hrect hseed hwide hoff hs choice br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
    initial batches hvalid blocks hlen a hdiag hord hplaced hmatched
  dsimp only at hphys
  have hscalar := fw_scalar_all_stages_first_band_gate n P hnlo hnhi hP
  dsimp only at hscalar
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hnum : (12 * Amax * (8 * (n : ℝ) + 96 * ((238 : ℝ) - P)) +
      ((n : ℝ) - ((12 * S : ℕ) : ℝ)) * Dmax) / N <
      (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * (poolMaximum n : ℝ) := by
    rw [fw_scalar_physical_envelope_identity n P hnlo hP (poolMaximum n : ℝ)]
    have hh := mul_lt_mul_of_pos_left hscalar.2.1 hX
    nlinarith
  constructor
  · intro row
    obtain ⟨q, hq, hcount, hline, hid, henv⟩ := hphys.1 row
    exact ⟨q, hq, hcount, hline, hid, lt_of_le_of_lt henv hnum⟩
  · intro col
    obtain ⟨q, hq, hcount, hline, hid, henv⟩ := hphys.2 col
    exact ⟨q, hq, hcount, hline, hid, lt_of_le_of_lt henv hnum⟩

end
end Sude
