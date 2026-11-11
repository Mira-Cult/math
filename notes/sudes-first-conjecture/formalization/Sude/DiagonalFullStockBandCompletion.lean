import Sude.DiagonalFullStockWidenedBands
import Sude.DiagonalFullStockWidenedCompletion

namespace Sude
noncomputable section

/-- Complete the same full-stock diagonal witness from an explicit original
reservation cover, outer bands, mean margins, and numerical RF gate. -/
theorem full_stock_dq_rf_from_mean_and_bands (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {n r₀ bits : ℕ} (a : Cell n ≃ Fin (n*n)) (reserved : Finset (Cell n))
    (m σ ε w : ℝ) (accounted shielded : Finset ℕ) (Dold : ℕ) (hε : 0 ≤ ε) (hn : 7 ≤ n) (hnmax : n ≤ 2^18)
    (hodd : Odd n) (hcenter : centralCell n (by omega) ∉ reserved)
    (hreserve : 4 * reserved.card ≤ n*n)
    (hload : 4 * (r₀ + 6*bits + 4) ≤ n)
    (hrowlo : ∀ i, r₀ ≤ (LayerPacking.rowUsed (reserved ∪ unreservedDiagonalCells reserved) i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed (reserved ∪ unreservedDiagonalCells reserved) i).card ≤ r₀ + (6*bits+4))
    (hcollo : ∀ i, r₀ ≤ (LayerPacking.colUsed (reserved ∪ unreservedDiagonalCells reserved) i).card)
    (hcolhi : ∀ i, (LayerPacking.colUsed (reserved ∪ unreservedDiagonalCells reserved) i).card ≤ r₀ + (6*bits+4))
    (hmean : |centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - m| ≤ σ * poolMaximum n)
    (hgap : σ + ε + 3 / (4 * (n : ℝ)) + w < 1/4)
    (hleft : 1 ≤ m - (σ + ε + 3 / (4 * (n : ℝ))) * poolMaximum n)
    (hright : m + (σ + ε + 3 / (4 * (n : ℝ))) * poolMaximum n ≤ poolMaximum n)
    (hcover : reserved.image (entry a) ⊆ accounted ∪ shielded)
    (haccount : accounted.card ≤ Dold)
    (hband : ∀ p ∈ shielded, (p : ℝ) ≤ m - (poolMaximum n : ℝ)/4 + w * poolMaximum n ∨
      m + (poolMaximum n : ℝ)/4 - w * poolMaximum n ≤ p)
    (hgate : (((9 * bits + 6) * n : ℕ) : ℝ) ≤
      (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
        Real.log (poolMaximum n) - (((Dold + (2*n - 1) : ℕ)) : ℝ)) :
    ∃ b c : Cell n ≃ Fin (n*n),
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      (∀ z ∈ reserved ∪ unreservedDiagonalCells reserved, entry c z = entry b z) ∧
      (∀ z ∈ reserved, entry c z = entry a z) ∧
      |(mainSum c : ℝ) - ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
        ((mainCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (poolMaximum n : ℝ) ∧
      |(antiSum c : ℝ) - ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
        ((antiCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (3/2 : ℝ) * poolMaximum n ∧
      (∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ reserved, (entry a z : ℝ)) +
        ((rowCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
      (∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ reserved, (entry a z : ℝ)) +
        ((columnCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
      2*n ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤ 3 * (poolMaximum n : ℝ) / (4*n) ∧
      mainSum c = mainSum b ∧ antiSum c = antiSum b ∧ Set.range (entry c) = pool n ∧ Function.Injective (entry c) := by
  have hend := old_widened_endpoints_from_mean a reserved m σ ε hmean hleft hright
  have hdel := old_reservation_widened_interval_from_bands a reserved accounted shielded m σ ε w Dold
    (by omega) hε hmean hgap hleft hcover haccount hband
  exact full_stock_dq_rf_from_widened_old bmor upper a reserved ε Dold hε hn hnmax hodd hcenter
    hreserve hload hrowlo hrowhi hcollo hcolhi hend.1 hend.2 hdel hgate


end
end Sude
