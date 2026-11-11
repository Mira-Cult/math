import Sude.FWFourFamilyLineCancellation
import Sude.FWFullReservationNonempty
import Sude.ReservedStageFamilyTotal
import Sude.ReservedPoolSignedMean
import Sude.FWReallocatedStageMeanSum
import Sude.FWSpareGlobalDeviationOfTheta
import Sude.FullReservationCancellationEnvelope

/-! Exact full-reservation unused mean and a family-sensitive bound on a
supplied reallocated square. No stock or witness-existence claim is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

private theorem scratch_full_mean_from_stages {n : ℕ} {I : Type*} [DecidableEq I]
    (a : Cell n ≃ Fin (n*n)) (full : Finset (Cell n))
    (stages : Finset I) (cells : I → Finset (Cell n)) (d : ℕ) (mean : I → ℝ)
    (hdis : Set.PairwiseDisjoint (↑stages : Set I) cells)
    (hcard : ∀ j ∈ stages, (cells j).card = 2*d*(n+8))
    (hsum : ∀ j ∈ stages, (∑ z ∈ cells j, (entry a z : ℝ)) = (2*d*(n+8) : ℕ) * mean j)
    (hsub : stages.biUnion cells ⊆ full) (hpos : 0 < (actualUnusedPool a full).card) :
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let A : ℝ := ∑ j ∈ stages, (mean j - μ)
    let D : ℝ := (∑ z ∈ full \ stages.biUnion cells, (entry a z : ℝ)) -
      ((full \ stages.biUnion cells).card : ℝ) * μ
    centralEntriesMean (actualUnusedPool a full) centralPoolValue - μ =
      -(2*(d : ℝ)*((n : ℝ)+8)*A+D) / (actualUnusedPool a full).card := by
  classical
  dsimp only
  let roles := stages.biUnion cells
  let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  have ht := reserved_uniform_stage_family_signed_total a stages cells d mean hdis hcard hsum
  dsimp only at ht
  have hparts : roles ∪ (full \ roles) = full := Finset.union_sdiff_of_subset hsub
  have hdisj : Disjoint roles (full \ roles) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact (Finset.mem_sdiff.mp hz').2 hz
  have hsplit : (∑ z ∈ full, (entry a z : ℝ)) - (full.card : ℝ)*μ =
      ((∑ z ∈ roles, (entry a z : ℝ)) - (roles.card : ℝ)*μ) +
      ((∑ z ∈ full \ roles, (entry a z : ℝ)) - ((full \ roles).card : ℝ)*μ) := by
    have hs := Finset.sum_union (f := fun z => (entry a z : ℝ)) hdisj
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hparts] at hs hc
    rw [hs, hc]
    push_cast
    ring
  have hup := actual_unused_mean_signed_update a full hpos
  change centralEntriesMean (actualUnusedPool a full) centralPoolValue = μ - _ at hup
  have ht' := ht.2
  change (∑ z ∈ roles, (entry a z : ℝ)) - (roles.card : ℝ)*μ = _ at ht'
  rw [hsplit, ht'] at hup
  change centralEntriesMean (actualUnusedPool a full) centralPoolValue - μ = _
  rw [hup]
  ring

theorem fw_four_family_exact_unused_mean {n P : ℕ}
    (hn : 19485 ≤ n)
    (hP : P ≤ 238)
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
    (a : Cell n ≃ Fin (n * n)) :
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
    centralEntriesMean (actualUnusedPool a full) centralPoolValue - μ =
      -(12 * ((n : ℝ)+8) * (∑ j, (means j - μ)) +
        ((∑ z ∈ full \ roles, (entry a z : ℝ)) - ((full \ roles).card : ℝ)*μ)) /
        (actualUnusedPool a full).card := by
  classical
  dsimp only
  let f := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  let cells := f ∘ fwFourStageInputEquiv n P
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
  let stages := fun j : FWFourStageIndex n P =>
    Finset.univ.image (fun x : Fin (6 * (n + 8)) × Bool => cells ((j, x.1), x.2))
  let means := fun j : FWFourStageIndex n P =>
    (∑ i, (((entry a (cells ((j, i), false)) : ℝ) + entry a (cells ((j, i), true))) / 2)) /
      ((6 * (n + 8) : ℕ) : ℝ)
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
  have ht := fw_four_family_stage_totals hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols a
  dsimp only at ht
  have hcover : Finset.univ.biUnion stages = roles := ht.2.2.2.2.2
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset (FWFourStageIndex n P)) : Set _) stages := by
    simpa only [Finset.coe_univ] using ht.2.2.1
  have hcard : ∀ j ∈ (Finset.univ : Finset (FWFourStageIndex n P)), (stages j).card = 2*6*(n+8) := by
    intro j _
    change (stages j).card = 12*(n+8)
    exact ht.2.2.2.1 j
  have hsum : ∀ j ∈ (Finset.univ : Finset (FWFourStageIndex n P)),
      (∑ z ∈ stages j, (entry a z : ℝ)) = (2*6*(n+8) : ℕ) * means j := by
    intro j _
    change (∑ z ∈ stages j, (entry a z : ℝ)) = ((12*(n+8) : ℕ) : ℝ) * means j
    exact ht.2.2.2.2.1 j
  have ho := fw_role_cell_occupancy hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  dsimp only at ho
  have hsub : Finset.univ.biUnion stages ⊆ full := by rw [hcover]; exact ho.1
  have hp := (fw_full_reservation_actual_unused_positive hn hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols a).2
  have h := scratch_full_mean_from_stages a full Finset.univ stages 6 means hdis hcard hsum hsub hp
  dsimp only at h ⊢
  rw [hcover] at h
  norm_num only at h
  exact h

end
end Sude

namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- The full unused mean is bounded using all family means and every spare
value, with the exact full-unused denominator. -/
theorem fw_reallocated_full_unused_mean_bound_of_theta
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
    |centralEntriesMean (actualUnusedPool new full) centralPoolValue - μ| ≤
      (12 * ((n : ℝ) + 8) * Amax + Dmax) / N := by
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
  have hocc := fw_role_cell_occupancy hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  have hcard : full.card = 12 * S * (n + 8) + 96 * (238 - P) := hocc.2.2.2.2.2.2.1
  have hpool := actualUnusedPool_card n new full
  have hpoolEq : (actualUnusedPool new full).card = n*n - (12*S*(n+8)+96*(238-P)) := by omega
  have hpoolReal : ((actualUnusedPool new full).card : ℝ) = N := by
    dsimp [N]; exact_mod_cast hpoolEq
  have hmean := fw_four_family_exact_unused_mean hnlo hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols new
  dsimp only at hmean
  change centralEntriesMean (actualUnusedPool new full) centralPoolValue - μ =
    -(12 * ((n : ℝ) + 8) * A + D) / ((actualUnusedPool new full).card : ℝ) at hmean
  change |centralEntriesMean (actualUnusedPool new full) centralPoolValue - μ| ≤
    (12 * ((n : ℝ) + 8) * Amax + Dmax) / N
  rw [hmean, hpoolReal, abs_div, abs_neg, abs_of_pos hN]
  apply div_le_div_of_nonneg_right _ (le_of_lt hN)
  calc
    |12 * ((n : ℝ) + 8) * A + D| ≤ |12 * ((n : ℝ) + 8) * A| + |D| := abs_add_le _ _
    _ = 12 * ((n : ℝ) + 8) * |A| + |D| := by rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 12 * ((n : ℝ) + 8))]
    _ ≤ 12 * ((n : ℝ) + 8) * Amax + Dmax := add_le_add (mul_le_mul_of_nonneg_left hA (by positivity)) hD

end
end Sude

