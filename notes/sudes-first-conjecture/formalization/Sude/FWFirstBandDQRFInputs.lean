import Sude.DQRFNetworkCompletionJoin

/-! The explicit DQ/RF premises for one chosen ordered square and its full
physical reservation. This package makes no claim that the premises hold. -/

namespace Sude
noncomputable section

/-- Inputs for DQ/RF completion, tied to one ordered square and geometric
reservation. The deletion budget uses the widened interval around that
square's actual unused-pool mean. -/
structure FWFirstBandDQRFInputs (n P bits Dold : ℕ) (hn : 0 < n)
    (ε : ℝ) (ordered : Cell n ≃ Fin (n*n)) (full : Finset (Cell n)) : Prop where
  epsilon_nonneg : 0 ≤ ε
  odd_order : Odd n
  center_free : centralCell n hn ∉ full
  reserve_capacity : 4 * full.card ≤ n*n
  load_capacity : 4 * (12*(5+16+3*(n/450)+P) + 6*bits + 4) ≤ n
  row_lower : ∀ i, 12*(5+16+3*(n/450)+P) ≤
    (LayerPacking.rowUsed (full ∪ unreservedDiagonalCells full) i).card
  row_upper : ∀ i, (LayerPacking.rowUsed (full ∪ unreservedDiagonalCells full) i).card ≤
    12*(5+16+3*(n/450)+P) + (6*bits+4)
  column_lower : ∀ i, 12*(5+16+3*(n/450)+P) ≤
    (LayerPacking.colUsed (full ∪ unreservedDiagonalCells full) i).card
  column_upper : ∀ i, (LayerPacking.colUsed (full ∪ unreservedDiagonalCells full) i).card ≤
    12*(5+16+3*(n/450)+P) + (6*bits+4)
  left_endpoint : 1 ≤ centralEntriesMean (actualUnusedPool ordered full) centralPoolValue -
    ε * poolMaximum n - 3 * (poolMaximum n : ℝ) / (4*n)
  right_endpoint : centralEntriesMean (actualUnusedPool ordered full) centralPoolValue +
    ε * poolMaximum n + 3 * (poolMaximum n : ℝ) / (4*n) ≤ poolMaximum n
  deleted : (apInterval
    (centralEntriesMean (actualUnusedPool ordered full) centralPoolValue - ε * poolMaximum n -
      3 * (poolMaximum n : ℝ) / (4*n))
    (centralEntriesMean (actualUnusedPool ordered full) centralPoolValue + ε * poolMaximum n +
      3 * (poolMaximum n : ℝ) / (4*n)) 2 1 ∩ full.image (entry ordered)).card ≤ Dold
  gate : (((9 * bits + 6) * n : ℕ) : ℝ) ≤
    (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
      Real.log (poolMaximum n) - (((Dold + (2*n - 1) : ℕ)) : ℝ)

end
end Sude
