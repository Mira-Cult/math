import Sude.CYDiagonalWidenedCompletion
import Sude.DiagonalFullStockWidenedBands
namespace Sude
noncomputable section

/-- Same-square sharp CY completion from explicit source mean, full-value
cover, outer bands, and the numerical stock gate. -/
theorem cy_dq_sharp_completion_from_mean_and_bands (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L) (hn : 7 ≤ n) (hnmax : n ≤ 2^18)
    (hodd : Odd n) (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols)
    (hload : 4*(2*(rows.length+cols.length)+4) ≤ n)
    (a : Cell n ≃ Fin (n*n)) (accounted shielded : Finset ℕ)
    (m σ ε w : ℝ) (Dold : ℕ) (hε : 0 ≤ ε)
    (hreserve : let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      4*full.card ≤ n*n)
    (hmean : let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      |centralEntriesMean (actualUnusedPool a full) centralPoolValue - m| ≤ σ * poolMaximum n)
    (hgap : σ + ε + 3/(4*(n : ℝ)) + w < 1/4)
    (hleft : 1 ≤ m - (σ+ε+3/(4*(n : ℝ)))*poolMaximum n)
    (hright : m + (σ+ε+3/(4*(n : ℝ)))*poolMaximum n ≤ poolMaximum n)
    (hcover : let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      full.image (entry a) ⊆ accounted ∪ shielded)
    (haccount : accounted.card ≤ Dold)
    (hband : ∀ p ∈ shielded, (p : ℝ) ≤ m - (poolMaximum n : ℝ)/4 + w * poolMaximum n ∨
      m + (poolMaximum n : ℝ)/4 - w * poolMaximum n ≤ p)
    (hgate : ((3*n+1 : ℕ) : ℝ) ≤
      (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
        Real.log (poolMaximum n) - (((Dold + (2*n-1) : ℕ)) : ℝ)) :
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
  have hends := old_widened_endpoints_from_mean a full m σ ε hmean hleft hright
  have hdel := old_reservation_widened_interval_from_bands a full accounted shielded m σ ε w Dold
    (by omega) hε hmean hgap hleft hcover haccount hband
  exact cy_dq_sharp_completion_from_widened_old bmor upper hs hL hn hnmax hodd choice rows cols
    hrows hcols hload a ε Dold hε hreserve hends.1 hends.2 hdel hgate
end
end Sude
