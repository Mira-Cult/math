import Sude.RFCompletionFreeResidual

/-! The synchronized reference agrees with the completed square on every
cell outside the full reservation. This transfers only its free-cell
residual, not the contribution of active roles or a complete line bound. -/
namespace Sude
noncomputable section

/-- An active-supported reference change cannot alter free-cell residuals. -/
theorem synchronized_reference_free_line_residual {n : ℕ}
    (c d : Cell n ≃ Fin (n*n)) (active reserved line : Finset (Cell n)) (μ : ℝ)
    (hsub : active ⊆ reserved)
    (hfixed : ∀ z ∉ active, entry d z = entry c z) :
    (∑ z ∈ line \ reserved, ((entry d z : ℝ) - μ)) =
      ∑ z ∈ line \ reserved, ((entry c z : ℝ) - μ) := by
  classical
  apply Finset.sum_congr rfl
  intro z hz
  have hz' : z ∉ active := fun ha => (Finset.mem_sdiff.mp hz).2 (hsub ha)
  rw [hfixed z hz']

/-- The RF strict free-residual bounds transfer to the same synchronized
reference and the same actual unused mean of the original ordered square. -/
theorem dq_rf_reference_free_residual {n bits : ℕ}
    (a c d : Cell n ≃ Fin (n*n)) (active reserved : Finset (Cell n)) (ε : ℝ)
    (hsub : active ⊆ reserved)
    (hcfix : ∀ z ∈ reserved, entry c z = entry a z)
    (hdfix : ∀ z ∉ active, entry d z = entry c z)
    (hrow : ∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ reserved, (entry a z : ℝ)) +
        ((rowCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)
    (hcol : ∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ reserved, (entry a z : ℝ)) +
        ((columnCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) :
    (∀ i, |∑ z ∈ rowCells i \ reserved, ((entry d z : ℝ) -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
    (∀ i, |∑ z ∈ columnCells i \ reserved, ((entry d z : ℝ) -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) := by
  have h := dq_rf_completion_free_residual a c reserved ε hcfix hrow hcol
  constructor
  · intro i
    rw [synchronized_reference_free_line_residual c d active reserved (rowCells i)
      (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue) hsub hdfix]
    exact h.1 i
  · intro i
    rw [synchronized_reference_free_line_residual c d active reserved (columnCells i)
      (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue) hsub hdfix]
    exact h.2 i

end
end Sude
