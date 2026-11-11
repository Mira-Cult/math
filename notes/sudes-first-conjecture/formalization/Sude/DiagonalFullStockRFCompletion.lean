import Sude.DiagonalFullStockExplicitMean
import Sude.CentralConstruct

namespace Sude
noncomputable section

/-- A selected DQ witness admits an RF continuation if its actual post-diagonal
analytic gate holds. The gate is neither constructed nor assumed globally. -/
theorem full_stock_dq_rf_conditional_completion_with_mean (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {n r₀ bits : ℕ} (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (ε : ℝ) (D : ℕ) (hε : 0 ≤ ε) (hn : 7 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hodd : Odd n) (hcenter : centralCell n (by omega) ∉ reserved)
    (hreserve : 4 * reserved.card ≤ n * n)
    (hload : 4 * (r₀ + 6 * bits + 4) ≤ n)
    (hrowlo : ∀ i, r₀ ≤ (LayerPacking.rowUsed (reserved ∪ unreservedDiagonalCells reserved) i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed (reserved ∪ unreservedDiagonalCells reserved) i).card ≤ r₀ + (6 * bits + 4))
    (hcollo : ∀ i, r₀ ≤ (LayerPacking.colUsed (reserved ∪ unreservedDiagonalCells reserved) i).card)
    (hcolhi : ∀ i, (LayerPacking.colUsed (reserved ∪ unreservedDiagonalCells reserved) i).card ≤ r₀ + (6 * bits + 4)) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      |(mainSum b : ℝ) - ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
        ((mainCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (poolMaximum n : ℝ) ∧
      |(antiSum b : ℝ) - ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
        ((antiCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (3 / 2 : ℝ) * poolMaximum n ∧
      2 * n ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
          (3 * (poolMaximum n : ℝ)) / (4 * n) ∧
      (PostDiagonalAnalyticInputs b reserved bits ε D →
        ∃ c : Cell n ≃ Fin (n * n),
          (∀ z ∈ reserved ∪ unreservedDiagonalCells reserved, entry c z = entry b z) ∧
          (∀ z ∈ reserved, entry c z = entry a z) ∧
          (∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ reserved, (entry a z : ℝ)) +
            ((rowCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
              (1 + 2 * (9 * bits + 6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
          (∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ reserved, (entry a z : ℝ)) +
            ((columnCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
              (1 + 2 * (9 * bits + 6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
          mainSum c = mainSum b ∧ antiSum c = antiSum b ∧
          Set.range (entry c) = pool n ∧ Function.Injective (entry c)) := by
  classical
  obtain ⟨b₀, b, _, hfixed, hmain, hanti, hcount, hmean, hline⟩ :=
    odd_full_stock_integrated_witness_explicit_mean a reserved hn hodd hcenter hreserve
  refine ⟨b, hfixed, hmain, hanti, hcount, hmean, ?_⟩
  intro hp
  have hdiags := postDiagonal_contains_both reserved
  obtain ⟨c, hfixedc, hrows, hcols, hmainc, hantic, hpool, hinj⟩ :=
    bmor_balanced_charged_completion bmor upper b (reserved ∪ unreservedDiagonalCells reserved)
      hdiags.1 hdiags.2 hload hrowlo hrowhi hcollo hcolhi ε D hε (by omega) hnmax
      hp.left hp.right hp.deletions hp.gate
  refine ⟨c, hfixedc, ?_, ?_, ?_, hmainc, hantic, hpool, hinj⟩
  · intro z hz
    exact (hfixedc z (Finset.mem_union_left _ hz)).trans (hfixed z hz)
  · intro i
    have ht := hline (rowCells i) (by simp [rowCells_card_exact]) (row_unreserved_diagonal_card_le_two reserved i)
    have hs := abs_sub_le (rowSum c i : ℝ)
      ((∑ z ∈ rowCells i ∩ (reserved ∪ unreservedDiagonalCells reserved), (entry b z : ℝ)) +
        ((rowCells i \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) *
          centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue)
      ((∑ z ∈ rowCells i ∩ reserved, (entry a z : ℝ)) +
        ((rowCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)
    linarith [hrows i]
  · intro i
    have ht := hline (columnCells i) (by simp [columnCells_card_exact]) (column_unreserved_diagonal_card_le_two reserved i)
    have hs := abs_sub_le (columnSum c i : ℝ)
      ((∑ z ∈ columnCells i ∩ (reserved ∪ unreservedDiagonalCells reserved), (entry b z : ℝ)) +
        ((columnCells i \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) *
          centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue)
      ((∑ z ∈ columnCells i ∩ reserved, (entry a z : ℝ)) +
        ((columnCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)
    linarith [hcols i]


/-- Compatibility wrapper retaining the original conditional RF interface. -/
theorem full_stock_dq_rf_conditional_completion (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {n r₀ bits : ℕ} (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (ε : ℝ) (D : ℕ) (hε : 0 ≤ ε) (hn : 7 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hodd : Odd n) (hcenter : centralCell n (by omega) ∉ reserved)
    (hreserve : 4 * reserved.card ≤ n * n)
    (hload : 4 * (r₀ + 6 * bits + 4) ≤ n)
    (hrowlo : ∀ i, r₀ ≤ (LayerPacking.rowUsed (reserved ∪ unreservedDiagonalCells reserved) i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed (reserved ∪ unreservedDiagonalCells reserved) i).card ≤ r₀ + (6 * bits + 4))
    (hcollo : ∀ i, r₀ ≤ (LayerPacking.colUsed (reserved ∪ unreservedDiagonalCells reserved) i).card)
    (hcolhi : ∀ i, (LayerPacking.colUsed (reserved ∪ unreservedDiagonalCells reserved) i).card ≤ r₀ + (6 * bits + 4)) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      |(mainSum b : ℝ) - ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
        ((mainCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (poolMaximum n : ℝ) ∧
      |(antiSum b : ℝ) - ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
        ((antiCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (3 / 2 : ℝ) * poolMaximum n ∧
      2 * n ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      (PostDiagonalAnalyticInputs b reserved bits ε D →
        ∃ c : Cell n ≃ Fin (n * n),
          (∀ z ∈ reserved ∪ unreservedDiagonalCells reserved, entry c z = entry b z) ∧
          (∀ z ∈ reserved, entry c z = entry a z) ∧
          (∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ reserved, (entry a z : ℝ)) +
            ((rowCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
              (1 + 2 * (9 * bits + 6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
          (∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ reserved, (entry a z : ℝ)) +
            ((columnCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
              (1 + 2 * (9 * bits + 6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
          mainSum c = mainSum b ∧ antiSum c = antiSum b ∧
          Set.range (entry c) = pool n ∧ Function.Injective (entry c)) := by
  obtain ⟨b, hfixed, hmain, hanti, hcount, _, hcontinue⟩ :=
    full_stock_dq_rf_conditional_completion_with_mean bmor upper a reserved ε D hε hn hnmax hodd hcenter
      hreserve hload hrowlo hrowhi hcollo hcolhi
  exact ⟨b, hfixed, hmain, hanti, hcount, hcontinue⟩

end
end Sude
