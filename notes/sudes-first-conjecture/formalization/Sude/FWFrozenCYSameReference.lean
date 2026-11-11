import Sude.FWCYSameReferenceCompletion
import Sude.FWFirstBandFrozenCYStockGate
import Sude.FWFirstBandFrozenCYEndpoints

/-! Same supplied FW reference and frozen first-band CY parameters. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem fw_frozen_cy_same_reference_completion
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
    (hmean : let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br++sr)++wr)++gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc++sc)++wc)++gc))
      |centralEntriesMean (actualUnusedPool a full) centralPoolValue -
        (Lucas.poolTotal n : ℝ)/(n*n : ℕ)| ≤ (11/100 : ℝ)*poolMaximum n) :
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
        (4+(7+1/(n : ℝ))*(4262317/50000000 : ℝ))*poolMaximum n) ∧
      (∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry a z : ℝ)) +
        ((columnCells i \ full).card : ℝ)*centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
        (4+(7+1/(n : ℝ))*(4262317/50000000 : ℝ))*poolMaximum n) ∧
      mainSum c = mainSum b ∧ antiSum c = antiSum b ∧
      Set.range (entry c) = pool n ∧ Function.Injective (entry c) := by
  have he := fw_first_band_frozen_cy_endpoints bmor lower upper hnlo hnhi
  dsimp only at he
  have hg := fw_first_band_frozen_cy_stock_gate bmor lower upper hnlo hnhi
  exact fw_cy_same_reference_completion bmor lower upper hnlo hnhi hodd hP
    hrect hseed hwide hoff hs choice br bc sr sc wr wc gr gc
    hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
    a batches hvalid candidates hcard kept hsub hkept blocks stages hlen trace hmatched hvalues
    (11/100 : ℝ) (4262317/50000000 : ℝ) (by norm_num) hmean he.1 he.2.1 he.2.2 hg
end
end Sude

