import Sude.FWNormalizedClassifiedCover
import Sude.CYDiagonalBandCompletion
import Sude.FWFullReservationQuarterCapacity
import Sude.FWPostDiagonalCompletionGeometry
import Sude.FWThetaInputs
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- On a supplied same-square FW reference with exact role values, derive the
classified full cover and apply conditional sharp CY completion. -/
theorem fw_cy_same_reference_completion
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n P : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hodd : Odd n) (hP : P ≤ 238)
    (hrect : 5*(4*6) ≤ fwJointRectangleCount n 254)
    (hseed : 5*(4*6)+16*(4*6) ≤ fwJointRectangleCount n 254)
    (hwide : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6) ≤ fwJointRectangleCount n 254)
    (hoff : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)+P*(4*6) ≤ fwJointRectangleCount n 254)
    (hs : 2*fwJointRectangleCount n 254+1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length=5*3) (hbc : bc.length=5*3)
    (hsr : sr.length=16*3) (hsc : sc.length=16*3)
    (hwr : wr.length=(3*(n/450))*3) (hwc : wc.length=(3*(n/450))*3)
    (hgr : gr.length=P*3) (hgc : gc.length=P*3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br++sr)++wr)++gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br++sr)++wr)++gr)))
      (((bc++sc)++wc)++gc))
    (a : Cell n ≃ Fin (n*n)) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card=17*(6*(n+8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card=16)
    (blocks : List DoublePair) (stages : List BTSelectedStage) (hlen : stages.length=P)
    {initial lastStock : Finset ℕ} {R last : ℕ}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial R lastStock last stages)
    (hmatched : let m : ℝ := (Lucas.poolTotal n : ℝ) / (n*n : ℕ)
      ∀ b ∈ blocks, b.MatchedValid (bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n)))
        (bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))))
    (hvalues : (fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)).image (entry a) =
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks ∪
        Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint))
    (σ ε : ℝ) (hε : 0 ≤ ε)
    (hmean : let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br++sr)++wr)++gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc++sc)++wc)++gc))
      |centralEntriesMean (actualUnusedPool a full) centralPoolValue -
        (Lucas.poolTotal n : ℝ)/(n*n : ℕ)| ≤ σ*poolMaximum n)
    (hgap : σ+ε+3/(4*(n : ℝ)) < 1/4)
    (hleft : 1 ≤ (Lucas.poolTotal n : ℝ)/(n*n : ℕ) - (σ+ε+3/(4*(n : ℝ)))*poolMaximum n)
    (hright : (Lucas.poolTotal n : ℝ)/(n*n : ℕ) + (σ+ε+3/(4*(n : ℝ)))*poolMaximum n ≤ poolMaximum n)
    (hgate : ((3*n+1 : ℕ) : ℝ) ≤
      (2*(ε*poolMaximum n)-(1036/125 : ℝ)*Real.sqrt (poolMaximum n))/Real.log (poolMaximum n) -
        (((12*(n+8)*5+12*(n+8)*254+(2*n-1) : ℕ)) : ℝ)) :
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br++sr)++wr)++gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc++sc)++wc)++gc))
    let final := full ∪ unreservedDiagonalCells full
    ∃ b c : Cell n ≃ Fin (n*n),
      (∀ z ∈ full, entry b z = entry a z) ∧
      (∀ z ∈ final, entry c z = entry b z) ∧
      (∀ z ∈ full, entry c z = entry a z) ∧
      |(mainSum c : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry a z : ℝ)) +
        ((mainCells n \ full).card : ℝ)*centralEntriesMean (actualUnusedPool a full) centralPoolValue)| ≤ (poolMaximum n : ℝ) ∧
      |(antiSum c : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry a z : ℝ)) +
        ((antiCells n \ full).card : ℝ)*centralEntriesMean (actualUnusedPool a full) centralPoolValue)| ≤ (3/2 : ℝ)*poolMaximum n ∧
      (∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry a z : ℝ)) +
        ((rowCells i \ full).card : ℝ)*centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
        (4+(7+1/(n : ℝ))*ε)*poolMaximum n) ∧
      (∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry a z : ℝ)) +
        ((columnCells i \ full).card : ℝ)*centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
        (4+(7+1/(n : ℝ))*ε)*poolMaximum n) ∧
      mainSum c = mainSum b ∧ antiSum c = antiSum b ∧
      Set.range (entry c) = pool n ∧ Function.Injective (entry c) := by
  classical
  let rows := (((br++sr)++wr)++gr)
  let cols := (((bc++sc)++wc)++gc)
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  let m : ℝ := (Lucas.poolTotal n : ℝ)/(n*n : ℕ)
  let ordinary := fwBridgeSeedProtectedValues batches candidates hcard kept hsub ∪
    Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint)
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
  let accounted := ordinary ∪ (full \ roles).image (entry a)
  let shielded := doubleBatchLow blocks ∪ doubleBatchHigh blocks
  have hXnat : 100 ≤ poolMaximum n := by
    have hp := fw_poolMaximum_gt_four_seed lower hnlo
    omega
  have hX : (100:ℝ) ≤ poolMaximum n := by exact_mod_cast hXnat
  have hm := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo (by omega)
  have hbridge : ∀ j < 5, (batches j).length = 3*(n+8) := fun j hj => (hvalid j hj).1.1
  have hc := fw_normalized_classified_full_value_cover hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
    a batches candidates hcard kept hsub blocks stages hlen hbridge hkept trace m (poolMaximum n) 0
    hX (by norm_num) hm.1 hm.2 hmatched hvalues
  have hreserve := fw_full_reservation_quarter_capacity hnlo hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  have hloadbase := fw_first_band_post_diagonal_load hnlo hnhi hP
  have hload : 4*(2*(rows.length+cols.length)+4) ≤ n := by
    dsimp [rows, cols]
    simp only [List.length_append, hbr,hbc,hsr,hsc,hwr,hwc,hgr,hgc]
    omega
  have hgap' : σ+ε+3/(4*(n : ℝ))+0 < 1/4 := by linarith
  have hleft' : 1 ≤ m-(σ+ε+3/(4*(n : ℝ)))*poolMaximum n := hleft
  have hright' : m+(σ+ε+3/(4*(n : ℝ)))*poolMaximum n ≤ poolMaximum n := hright
  exact cy_dq_sharp_completion_from_mean_and_bands bmor upper hs (by simp [fwJointRectangleCount]; omega)
    (by omega) (by omega) hodd choice rows cols hrows hcols hload a accounted shielded m σ ε 0
    (12*(n+8)*5+12*(n+8)*254) hε hreserve hmean hgap' hleft' hright' hc.1 hc.2.1 hc.2.2 hgate
end
end Sude
