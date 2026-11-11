import Sude.FWReservedMidpointRow
import Sude.FWFourStageRectangleMeansOfTheta
import Sude.FWFirstBandReallocatedCancellationGate
import Sude.ReservedMidpointCancellationAlgebra
import Sude.FWPhysicalRowIncidence

/-! The first-band physical row invoice, local stage/spare contribution and
scalar cancellation, retaining the complete free-cell residual. No free-cell
bound, final numerical gate, diagonal or later-flow conclusion is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem fw_first_band_row_residual_bound
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} {stages : List BTSelectedStage} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hP : stages.length ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseedrect : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + stages.length * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (source ordered : Cell n ≃ Fin (n*n))
    (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hdiag : ∀ t side, entry source (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hord : ∀ x, entry source (fwBridgeLayerCells br bc hbr hbc x) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x))
    (hplaced : ∀ x : FWWideInputs n, entry source (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8)))) (sb : Fin 5 → Fin (3 * (n + 8)) → Bool)
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (sw : Fin (3 * (n / 450)) → Fin (3 * (n + 8)) → Bool)
    (hbridge : ∀ j b p side, entry ordered (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,b,p),side)) =
      entry source (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,πb j b,doubleBlockPairSwap (sb j b) p),side)))
    (hwideEntry : ∀ j b p side, entry ordered (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),side)) =
      entry source (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,πw j b,doubleBlockPairSwap (sw j b) p),side)))
    (hpairgap : ∀ j i, entry ordered (btGrowingOffsetPairCells
      (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc ((j,i),true)) =
      entry ordered (btGrowingOffsetPairCells
        (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc ((j,i),false)) + (stages.get j).gap)
    (hseedgap : ∀ j q, entry ordered (fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc ((j,q),true)) =
       entry ordered (fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc ((j,q),false)) + 2)
    (vr : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) ordered)
    (vc : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (LayerPacking.transposePlacement ordered))
    (networkR : CenteredNetwork (Fin 3 × Fin n) (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) vr)
    (blocksC : (Fin 3 × Fin n) → Finset (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n))
    (hslotr : ∀ t side, rowNetworkSlot vr (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hslotc : ∀ t side, rowNetworkSlot vc (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (hblockr : ∀ edge, networkR.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (hblockc : ∀ edge, blocksC edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2)))
    (reference : Cell n ≃ Fin (n*n)) (r : Fin n)
    (hinvoice : |2 * (rowSum reference r : ℝ) -
      (physicalNetworkMidpointTwice vr networkR r : ℝ)| ≤ 9)
    (B W U V : ℝ)
    (hB : |doubleBlockActualCenteredScore (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
      (fun z => z ∈ (rowCells r)) source ordered| ≤ B)
    (hW : |doubleBlockActualCenteredScore (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
      (fun z => z ∈ (rowCells r)) source ordered| ≤ W)
    (hseed :
      let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
      let mean := fun j : FWFourStageIndex n stages.length =>
        (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
          ((6 * (n + 8) : ℕ) : ℝ)
      let seed := fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc
      |(∑ z ∈ (rowCells r) ∩ Finset.univ.image seed, (entry ordered z : ℝ)) -
        (∑ j : Fin 16, ∑ i : Fin (6*(n+8)), physicalPairLineWeight seed (fun z => z ∈ (rowCells r)) (j,i) *
          mean (Sum.inl (Sum.inl (Sum.inr j))))| ≤ U)
    (hgrowth :
      let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
      let mean := fun j : FWFourStageIndex n stages.length =>
        (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
          ((6 * (n + 8) : ℕ) : ℝ)
      let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
      |(∑ z ∈ (rowCells r) ∩ Finset.univ.image growth, (entry ordered z : ℝ)) -
        (∑ j : Fin stages.length, ∑ i : Fin (6*(n+8)), physicalPairLineWeight growth (fun z => z ∈ (rowCells r)) (j,i) * mean (Sum.inr j))| ≤ V) :
    let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
    let mean := fun j : FWFourStageIndex n stages.length =>
        (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
          ((6 * (n + 8) : ℕ) : ℝ)
    let roles := fwGrowthEarlyRoleCells hrect hseedrect hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let ν := centralEntriesMean (actualUnusedPool ordered full) centralPoolValue
    |(rowSum reference r : ℝ) - ((n : ℝ) * μ +
      ∑ z ∈ (rowCells r) \ full, ((entry ordered z : ℝ) - ν))| ≤
      (9 : ℝ) / 2 + B + W + U + V +
        (257 / 250 : ℝ) * (poolMaximum n : ℝ) +
        (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * (poolMaximum n : ℝ) := by
  classical
  let cells := fwFourFamilyPairCells hrect hseedrect hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
  let means := fun j : FWFourStageIndex n stages.length =>
    (∑ i, (((entry ordered (cells ((j,i),false)) : ℝ) + entry ordered (cells ((j,i),true))) / 2)) /
      ((6 * (n + 8) : ℕ) : ℝ)
  let roles := fwGrowthEarlyRoleCells hrect hseedrect hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
  let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  let ν := centralEntriesMean (actualUnusedPool ordered full) centralPoolValue
  let A : ℝ := ∑ j, (means j - μ)
  let spare := rowCells r ∩ (full \ roles)
  let free := rowCells r \ full
  let weight := fun j i => physicalPairLineWeight cells (fun z => z ∈ rowCells r) (j,i)
  let localBound : ℝ := (257 / 250 : ℝ) * (poolMaximum n : ℝ)
  let cancelBound : ℝ := (19033 / 450 : ℝ) * (201 / 10000 : ℝ) * (poolMaximum n : ℝ)
  have hrow := fw_reserved_midpoint_row hP hrect hseedrect hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols source ordered
    πb sb πw sw hbridge hwideEntry hpairgap hseedgap vr vc networkR blocksC hslotr hslotc hblockr hblockc
    reference r hinvoice B W U V hB hW hseed hgrowth
  have hlocalAll := fw_four_stage_weighted_spare_deviation_of_theta bmor lower upper hnlo (by omega) hP
    hrect hseedrect hwide hoff hs choice br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols ordered
  have hgeo := fw_physical_row_incidence hP hrect hseedrect hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols r (fun z => (entry ordered z : ℝ) - μ)
  have hgate := fw_first_band_reallocated_cancellation_gate bmor lower upper hnlo hnhi hP
    hrect hseedrect hwide hoff hs choice br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
    initial batches hvalid blocks hlen source ordered hdiag hord hplaced hmatched πb sb πw sw hbridge hwideEntry
  dsimp only at hrow hlocalAll hgeo hgate
  obtain ⟨q, hq, hcount, hline, hid, hbound⟩ := hgate.1 r
  have hfreeCard : free.card = n - 12 * (5 + 16 + 3 * (n / 450) + stages.length) - q := by
    dsimp [free]
    rw [hgeo.2.2, hcount]
    omega
  have hcancel : |12 * A + (free.card : ℝ) * (ν - μ)| ≤ cancelBound := by
    rw [hfreeCard]
    exact le_of_lt hbound
  have hlocal : |(∑ j, ∑ i, weight j i * (means j - μ)) - 12 * A +
      (∑ z ∈ spare, ((entry ordered z : ℝ) - μ))| ≤ localBound := by
    have hl := hlocalAll.1 r
    have hlinePred : (fun z : Cell n => z ∈ rowCells r) = (fun z : Cell n => z.1 = r) := by
      funext z; exact propext (mem_rowCells r z)
    change |(∑ j, ∑ i, physicalPairLineWeight cells (fun z => z.1 = r) (j,i) * (means j - μ)) -
      12 * A + (∑ i ∈ LayerPacking.rowUsed
        (packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n stages.length hP)) r,
        ((entry ordered (r,i) : ℝ) - μ))| ≤ localBound at hl
    rw [← hgeo.2.1] at hl
    simpa only [weight, hlinePred, spare] using hl
  have hincidence : (∑ j, ∑ i, weight j i) + (spare.card : ℝ) + (free.card : ℝ) = (n : ℝ) := by
    have htotal := hgeo.1
    have hspare : (spare.card : ℝ) =
        (LayerPacking.rowUsed (packedRectangleSupport hs choice \ activeRectangleSupport hs choice
          (fwActiveRectangleLabels n stages.length hP)) r).card := by
      have hh := hgeo.2.1
      -- The same set identity is used with the constant-one value.
      have hc := fw_physical_row_incidence hP hrect hseedrect hwide hoff hs choice
        br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols r (fun _ => (1 : ℝ))
      dsimp only at hc
      have hsum := hc.2.1
      change (∑ z ∈ spare, (1 : ℝ)) = ∑ i ∈ LayerPacking.rowUsed
        (packedRectangleSupport hs choice \ activeRectangleSupport hs choice
          (fwActiveRectangleLabels n stages.length hP)) r, (1 : ℝ) at hsum
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hsum
    have hlinePred : (fun z : Cell n => z ∈ rowCells r) = (fun z : Cell n => z.1 = r) := by
      funext z; exact propext (mem_rowCells r z)
    have hfree := hgeo.2.2
    have hfullle : (LayerPacking.rowUsed full r).card ≤ n := by
      rw [hcount]
      omega
    have hcast : ((free.card : ℕ) : ℝ) = (n : ℝ) - (LayerPacking.rowUsed full r).card := by
      dsimp [free]
      rw [hfree, Nat.cast_sub hfullle]
    simp only [weight, hlinePred] at *
    rw [hspare, hcast]
    linarith
  exact finite_reserved_midpoint_cancellation weight means (fun z => (entry ordered z : ℝ)) spare free
    (rowSum reference r : ℝ) n μ ν A ((9 : ℝ) / 2 + B + W + U + V) localBound cancelBound
    hrow hlocal hcancel hincidence

end
end Sude
