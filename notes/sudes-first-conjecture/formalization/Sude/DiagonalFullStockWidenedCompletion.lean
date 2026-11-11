import Sude.DiagonalFullStockRFCompletion
import Sude.DiagonalFullStockPostInputs
namespace Sude
noncomputable section

/-- Full-stock diagonal placement and RF completion from explicit old-pool
endpoint margins, widened-interval deletion budget and the numerical gate.
The construction uses the same chosen diagonal witness throughout. -/
theorem full_stock_dq_rf_from_widened_old (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {n r₀ bits : ℕ} (a : Cell n ≃ Fin (n*n)) (reserved : Finset (Cell n))
    (ε : ℝ) (Dold : ℕ) (hε : 0 ≤ ε) (hn : 7 ≤ n) (hnmax : n ≤ 2^18)
    (hodd : Odd n) (hcenter : centralCell n (by omega) ∉ reserved)
    (hreserve : 4 * reserved.card ≤ n*n)
    (hload : 4 * (r₀ + 6*bits + 4) ≤ n)
    (hrowlo : ∀ i, r₀ ≤ (LayerPacking.rowUsed (reserved ∪ unreservedDiagonalCells reserved) i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed (reserved ∪ unreservedDiagonalCells reserved) i).card ≤ r₀ + (6*bits+4))
    (hcollo : ∀ i, r₀ ≤ (LayerPacking.colUsed (reserved ∪ unreservedDiagonalCells reserved) i).card)
    (hcolhi : ∀ i, (LayerPacking.colUsed (reserved ∪ unreservedDiagonalCells reserved) i).card ≤ r₀ + (6*bits+4))
    (hleft : 1 ≤ centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n -
      3 * (poolMaximum n : ℝ) / (4*n))
    (hright : centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n +
      3 * (poolMaximum n : ℝ) / (4*n) ≤ poolMaximum n)
    (hdeleted : (apInterval
      (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n - 3 * (poolMaximum n : ℝ) / (4*n))
      (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n + 3 * (poolMaximum n : ℝ) / (4*n))
      2 1 ∩ reserved.image (entry a)).card ≤ Dold)
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
  obtain ⟨b, hfixed, hmain, hanti, hcount, hmean, hcontinue⟩ :=
    full_stock_dq_rf_conditional_completion_with_mean bmor upper a reserved ε (Dold + (2*n-1))
      hε hn hnmax hodd hcenter hreserve hload hrowlo hrowhi hcollo hcolhi
  have hp : PostDiagonalAnalyticInputs b reserved bits ε (Dold + (2*n-1)) :=
    post_diagonal_inputs_from_widened_old a b reserved ε (3 * (poolMaximum n : ℝ) / (4*n)) Dold
      (by omega) hodd hε hfixed hmean hleft hright hdeleted hgate
  obtain ⟨c, hfixedc, hfixeda, hrows, hcols, hmainc, hantic, hpool, hinj⟩ := hcontinue hp
  refine ⟨b, c, hfixed, hfixedc, hfixeda, ?_, ?_, hrows, hcols, hcount, hmean, hmainc, hantic, hpool, hinj⟩
  · simpa [hmainc] using hmain
  · simpa [hantic] using hanti
end
end Sude
