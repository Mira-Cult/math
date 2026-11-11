import Sude.FWClassifiedFullCover
import Sude.CYDiagonalBandCompletion

namespace Sude
noncomputable section

/-- Same-square sharp CY completion with classified full keepout values.
The role image, spare count, mean and numerical stock gate remain inputs. -/
theorem cy_dq_completion_from_classified_cover (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {L n P g : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L) (hn : 7 ≤ n) (hnmax : n ≤ 2^18)
    (hodd : Odd n) (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols)
    (hload : 4*(2*(rows.length+cols.length)+4) ≤ n)
    (a : Cell n ≃ Fin (n*n)) (roles : Finset (Cell n))
    (batches : ℕ → List DoublePair) (hlenBridge : ∀ j < 5, (batches j).length = 3*(n+8))
    (candidates : Finset ℕ) (hcard : candidates.card = 17*(6*(n+8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    {initial lastStock : Finset ℕ} {R last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g (6*(n+8)) initial R lastStock last stages)
    (hlen : stages.length = P) (hP : P ≤ 238)
    (blocks : List DoublePair) (m σ ε w : ℝ) (hε : 0 ≤ ε) (hw : 0 ≤ w)
    (hX : 100 ≤ (poolMaximum n : ℝ))
    (hmlo : (243 / 500 : ℝ)*poolMaximum n ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ)*poolMaximum n)
    (hmatched : ∀ b ∈ blocks, b.MatchedValid
      (bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))))
    (hreserve : let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      4*full.card ≤ n*n)
    (hmean : let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      |centralEntriesMean (actualUnusedPool a full) centralPoolValue - m| ≤ σ * poolMaximum n)
    (hgap : σ + ε + 3/(4*(n : ℝ)) + w < 1/4)
    (hleft : 1 ≤ m - (σ+ε+3/(4*(n : ℝ)))*poolMaximum n)
    (hright : m + (σ+ε+3/(4*(n : ℝ)))*poolMaximum n ≤ poolMaximum n)
    (hroles : roles.image (entry a) ⊆
      (fwBridgeSeedProtectedValues batches candidates hcard kept hsub ∪
        (doubleBatchLow blocks ∪ doubleBatchHigh blocks)) ∪
        Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint))
    (hspare : let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      (full \ roles).card ≤ 96*(238-P))
    (hgate : ((3*n+1 : ℕ) : ℝ) ≤
      (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
        Real.log (poolMaximum n) - ((((12*(n+8)*5 + 12*(n+8)*254) + (2*n-1) : ℕ)) : ℝ)) :
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)
    let final := full ∪ unreservedDiagonalCells full
    ∃ b c : Cell n ≃ Fin (n*n),
      (∀ z ∈ full, entry b z = entry a z) ∧
      (∀ z ∈ final, entry c z = entry b z) ∧
      (∀ z ∈ full, entry c z = entry a z) ∧
      |(mainSum c : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry a z : ℝ)) +
        ((mainCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool a full) centralPoolValue)| ≤ (poolMaximum n : ℝ) ∧
      |(antiSum c : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry a z : ℝ)) +
        ((antiCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool a full) centralPoolValue)| ≤ (3/2 : ℝ)*poolMaximum n ∧
      (∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry a z : ℝ)) +
        ((rowCells i \ full).card : ℝ) * centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
        (4+(7+1/(n : ℝ))*ε)*poolMaximum n) ∧
      (∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry a z : ℝ)) +
        ((columnCells i \ full).card : ℝ) * centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
        (4+(7+1/(n : ℝ))*ε)*poolMaximum n) ∧
      mainSum c = mainSum b ∧ antiSum c = antiSum b ∧
      Set.range (entry c) = pool n ∧ Function.Injective (entry c) := by
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  let ordinary := fwBridgeSeedProtectedValues batches candidates hcard kept hsub ∪
    Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint)
  let accounted := ordinary ∪ (full \ roles).image (entry a)
  let shielded := doubleBatchLow blocks ∪ doubleBatchHigh blocks
  have hc := fw_classified_full_value_cover hP a full roles batches hlenBridge candidates hcard kept hsub hkept
    trace hlen blocks m (poolMaximum n) w hX hw hmlo hmhi hmatched hroles hspare
  exact cy_dq_sharp_completion_from_mean_and_bands bmor upper hs hL hn hnmax hodd choice rows cols
    hrows hcols hload a accounted shielded m σ ε w (12*(n+8)*5 + 12*(n+8)*254) hε
    hreserve hmean hgap hleft hright hc.1 hc.2.1 hc.2.2 hgate

end
end Sude
