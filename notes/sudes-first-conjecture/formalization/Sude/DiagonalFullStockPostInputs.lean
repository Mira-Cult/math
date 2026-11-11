import Sude.DiagonalFullStockIntervalShift
import Sude.CentralConstruct
namespace Sude
noncomputable section

/-- Conditional post-diagonal inputs from the old actual mean and an explicit
budget for the old reservation in a widened interval. No gate is derived. -/
theorem post_diagonal_inputs_from_widened_old {n bits : ℕ}
    (a b : Cell n ≃ Fin (n*n)) (reserved : Finset (Cell n))
    (ε δ : ℝ) (Dold : ℕ) (hn : 0 < n) (hodd : Odd n)
    (hε : 0 ≤ ε) (hfixed : ∀ z ∈ reserved, entry b z = entry a z)
    (hshift : |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
      centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤ δ)
    (hleft : 1 ≤ centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n - δ)
    (hright : centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n + δ ≤ poolMaximum n)
    (hdeleted : (apInterval
      (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n - δ)
      (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n + δ)
      2 1 ∩ reserved.image (entry a)).card ≤ Dold)
    (hgate : (((9 * bits + 6) * n : ℕ) : ℝ) ≤
      (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
        Real.log (poolMaximum n) - (((Dold + (2*n - 1) : ℕ)) : ℝ)) :
    PostDiagonalAnalyticInputs b reserved bits ε (Dold + (2*n - 1)) := by
  have hr : 0 ≤ ε * (poolMaximum n : ℝ) := mul_nonneg hε (by positivity)
  have hm := abs_le.mp hshift
  have hdel := post_diagonal_deletions_from_widened_interval a b reserved
    (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)
    (centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue)
    (ε * poolMaximum n) δ hn hodd hfixed hr hshift (by linarith)
  refine ⟨?_, ?_, ?_, hgate⟩
  · linarith [hm.1]
  · linarith [hm.2]
  · omega
end
end Sude
