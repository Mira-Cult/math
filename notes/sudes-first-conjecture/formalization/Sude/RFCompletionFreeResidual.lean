import Sude.DQRFNetworkCompletionJoin

/-! Exact free-cell residuals from a supplied RF completion. The reference
mean is the actual unused mean of the original ordered square and the same
geometric reservation. No completion, stock, or line bound is constructed. -/
namespace Sude
noncomputable section

/-- For a completed placement fixing the reservation, its line discrepancy
from the original reserved values and unused mean is exactly the centered
sum of its free entries. -/
theorem fixed_reservation_free_line_residual {n : ℕ}
    (a c : Cell n ≃ Fin (n*n)) (reserved line : Finset (Cell n)) (μ : ℝ)
    (hfixed : ∀ z ∈ reserved, entry c z = entry a z) :
    (∑ z ∈ line, (entry c z : ℝ)) -
      ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) + ((line \ reserved).card : ℝ) * μ) =
      ∑ z ∈ line \ reserved, ((entry c z : ℝ) - μ) := by
  classical
  have hsplit := Finset.sum_inter_add_sum_sdiff line reserved (fun z => (entry c z : ℝ))
  have hres : (∑ z ∈ line ∩ reserved, (entry c z : ℝ)) =
      ∑ z ∈ line ∩ reserved, (entry a z : ℝ) := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [hfixed z (Finset.mem_inter.mp hz).2]
  rw [hres] at hsplit
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  linarith

/-- The conditional DQ/RF row and column estimates give the very same strict
bound on centered free cells, on the completed square and original full
reservation. The supplied estimates and fixedness may be taken directly from
`dq_rf_network_completion_join` or `full_stock_dq_rf_from_widened_old`. -/
theorem dq_rf_completion_free_residual {n bits : ℕ}
    (a c : Cell n ≃ Fin (n*n)) (reserved : Finset (Cell n)) (ε : ℝ)
    (hfixed : ∀ z ∈ reserved, entry c z = entry a z)
    (hrow : ∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ reserved, (entry a z : ℝ)) +
        ((rowCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)
    (hcol : ∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ reserved, (entry a z : ℝ)) +
        ((columnCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) :
    (∀ i, |∑ z ∈ rowCells i \ reserved, ((entry c z : ℝ) -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
    (∀ i, |∑ z ∈ columnCells i \ reserved, ((entry c z : ℝ) -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) := by
  constructor
  · intro i
    have h := fixed_reservation_free_line_residual a c reserved (rowCells i)
      (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue) hfixed
    rw [← rowSum_real_cells c i] at h
    rw [← h]
    exact hrow i
  · intro i
    have h := fixed_reservation_free_line_residual a c reserved (columnCells i)
      (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue) hfixed
    rw [← columnSum_real_cells c i] at h
    rw [← h]
    exact hcol i

end
end Sude
