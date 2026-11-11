import Sude.FWReservedMidpointColumn
import Sude.FWFourStageRectangleMeansOfTheta
import Sude.FWFirstBandReallocatedCancellationGate
import Sude.ReservedMidpointCancellationAlgebra
import Sude.FWPhysicalColumnIncidence

/-! Same-square column midpoint cancellation with an explicit free residual.
The supplied midpoint bound may be obtained from `fw_reserved_midpoint_column`.
No free-residual estimate, total numerical gate, or later flow is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

theorem fw_column_midpoint_theta_cancellation
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
      entry old (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,πw j b,doubleBlockPairSwap (sw j b) p),side)))
    (reference : Cell n ≃ Fin (n*n)) (c : Fin n) (E : ℝ)
    (hmid :
      let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
      let means := fun j : FWFourStageIndex n P =>
        (∑ i, (((entry new (cells ((j,i),false)) : ℝ) + entry new (cells ((j,i),true))) / 2)) /
          ((6 * (n + 8) : ℕ) : ℝ)
      let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
        Finset.univ.image (btGrowingOffsetCells
          (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
      let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
      |(columnSum reference c : ℝ) - ((∑ j : FWFourStageIndex n P, ∑ i : Fin (6*(n+8)),
        physicalPairLineWeight cells (fun z => z.2 = c) (j,i) * means j) +
        (∑ z ∈ columnCells c ∩ (full \ roles), (entry new z : ℝ)) +
        (∑ z ∈ columnCells c \ full, (entry new z : ℝ)))| ≤ E) :
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let ν := centralEntriesMean (actualUnusedPool new full) centralPoolValue
    |(columnSum reference c : ℝ) - ((n : ℝ) * μ +
      ∑ z ∈ columnCells c \ full, ((entry new z : ℝ) - ν))| ≤
        E + (257 / 250 : ℝ) * (poolMaximum n : ℝ) +
          (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * (poolMaximum n : ℝ) := by
  classical
  dsimp only at hmid ⊢
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
  let means := fun j : FWFourStageIndex n P =>
    (∑ i, (((entry new (cells ((j,i),false)) : ℝ) + entry new (cells ((j,i),true))) / 2)) /
      ((6 * (n + 8) : ℕ) : ℝ)
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
  let spare := packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
  let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  let ν := centralEntriesMean (actualUnusedPool new full) centralPoolValue
  let A : ℝ := ∑ j, (means j - μ)
  let S := 5 + 16 + 3 * (n / 450) + P
  have hi := fw_physical_column_incidence hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols c (fun z => (entry new z : ℝ) - μ)
  have hi1 := fw_physical_column_incidence hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols c (fun _ => (1 : ℝ))
  dsimp only at hi hi1
  have hcard : ((columnCells c ∩ (full \ roles)).card : ℝ) = (LayerPacking.colUsed spare c).card := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hi1.2.1
  have hlocal := (fw_four_stage_weighted_spare_deviation_of_theta bmor lower upper hnlo (by omega) hP
    hrect hseed hwide hoff hs choice br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols new).2 c
  dsimp only at hlocal
  have hlocal' : |(∑ j : FWFourStageIndex n P, ∑ i : Fin (6*(n+8)),
      physicalPairLineWeight cells (fun z => z.2 = c) (j,i) * (means j - μ)) - 12 * A +
      (∑ z ∈ columnCells c ∩ (full \ roles), ((entry new z : ℝ) - μ))| ≤
        (257 / 250 : ℝ) * (poolMaximum n : ℝ) := by
    rw [hi.2.1]
    exact hlocal
  obtain ⟨q, hq, hcount, hle, heq, hgate⟩ :=
    (fw_first_band_reallocated_cancellation_gate bmor lower upper hnlo hnhi hP
      hrect hseed hwide hoff hs choice br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
      initial batches hvalid blocks hlen old new hdiag hord hplaced hmatched πb sb πw sw hbridge hwideEntry).2 c
  have hfree : (columnCells c \ full).card = n - 12 * S - q := by
    rw [hi.2.2, hcount]
    omega
  have hcancel : |12 * A + ((columnCells c \ full).card : ℝ) * (ν - μ)| ≤
      (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * (poolMaximum n : ℝ) := by
    rw [hfree]
    exact le_of_lt hgate
  have hincidence : (∑ j : FWFourStageIndex n P, ∑ i : Fin (6*(n+8)),
      physicalPairLineWeight cells (fun z => z.2 = c) (j,i)) +
        ((columnCells c ∩ (full \ roles)).card : ℝ) + ((columnCells c \ full).card : ℝ) = n := by
    rw [hcard, hi.2.2]
    have hn : (LayerPacking.colUsed full c).card ≤ n := by
      rw [hcount]
      omega
    have hh : ((n - (LayerPacking.colUsed full c).card : ℕ) : ℝ) = (n : ℝ) - (LayerPacking.colUsed full c).card := by
      rw [Nat.cast_sub hn]
    rw [hh]
    linarith [hi.1]
  exact finite_reserved_midpoint_cancellation
    (fun j i => physicalPairLineWeight cells (fun z => z.2 = c) (j,i)) means
    (fun z => (entry new z : ℝ)) (columnCells c ∩ (full \ roles)) (columnCells c \ full)
    (columnSum reference c : ℝ) n μ ν A E ((257 / 250 : ℝ) * (poolMaximum n : ℝ))
    ((19033 / 450 : ℝ) * (201 / 10000 : ℝ) * (poolMaximum n : ℝ))
    hmid hlocal' hcancel hincidence

end
end Sude
