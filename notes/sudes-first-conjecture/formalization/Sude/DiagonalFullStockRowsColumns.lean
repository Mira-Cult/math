import Sude.DiagonalFullStockGeometry
import Sude.DiagonalLineTransfer

/-! DQ2's 3X expectation invoice on every actual row and column. -/
namespace Sude
noncomputable section

/-- One full-stock diagonal placement preserves the original reservation,
leaves at least 2n unused entries, and changes every row and column's
conditional completion expectation by at most 3X. This is not a bound on
the completed line sums, nor a statement about the two diagonal sums. -/
theorem odd_full_stock_rows_columns_expectation {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (hn : 7 ≤ n) (hodd : Odd n)
    (hcenter : centralCell n (by omega) ∉ reserved) (hreserve : 4 * reserved.card ≤ n * n) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      2 * n ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      (∀ r : Fin n,
        |((∑ z ∈ rowCells r ∩ (reserved ∪ unreservedDiagonalCells reserved), (entry b z : ℝ)) +
            ((rowCells r \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) *
              centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue) -
          ((∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) +
            ((rowCells r \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          3 * (poolMaximum n : ℝ)) ∧
      (∀ c : Fin n,
        |((∑ z ∈ columnCells c ∩ (reserved ∪ unreservedDiagonalCells reserved), (entry b z : ℝ)) +
            ((columnCells c \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) *
              centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue) -
          ((∑ z ∈ columnCells c ∩ reserved, (entry a z : ℝ)) +
            ((columnCells c \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          3 * (poolMaximum n : ℝ)) := by
  obtain ⟨b, hfixed, hstock, hline⟩ :=
    odd_diagonal_full_stock_three_x a reserved hn hodd hcenter hreserve
  refine ⟨b, hfixed, hstock, ?_, ?_⟩
  · intro r
    exact hline (rowCells r) (by simp [rowCells_card_exact])
      (row_unreserved_diagonal_card_le_two reserved r)
  · intro c
    exact hline (columnCells c) (by simp [columnCells_card_exact])
      (column_unreserved_diagonal_card_le_two reserved c)

end
end Sude
