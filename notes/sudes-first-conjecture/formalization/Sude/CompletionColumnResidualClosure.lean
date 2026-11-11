import Sude.CompletedReservationSamePoolResidual

/-! Close a supplied same-completion column residual estimate using its explicit
DQ/RF completion bound. This does not construct a completion or prove a final
numerical threshold, primality, or any later-flow property. -/
namespace Sude
noncomputable section

/-- The completed square fixes this exact reservation, so the DQ/RF column
estimate bounds the free residual around the completed square's unused mean.
One supplied midpoint residual comparison then gives the displayed strict column
bound for the same reference. All witness and analytic inputs remain explicit. -/
theorem completion_column_residual_closure {n bits : ℕ}
    (a c reference : Cell n ≃ Fin (n*n)) (full : Finset (Cell n))
    (j : Fin n) (ε μ K : ℝ)
    (hfixed : ∀ z ∈ full, entry c z = entry a z)
    (hcompletion : |(columnSum c j : ℝ) - ((∑ z ∈ columnCells j ∩ full, (entry a z : ℝ)) +
        ((columnCells j \ full).card : ℝ) * centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)
    (hcomparison : |(columnSum reference j : ℝ) - ((n : ℝ) * μ +
        ∑ z ∈ columnCells j \ full, ((entry c z : ℝ) -
          centralEntriesMean (actualUnusedPool c full) centralPoolValue))| ≤ K) :
    |(columnSum reference j : ℝ) - (n : ℝ) * μ| <
      K + ((1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) := by
  classical
  let ν := centralEntriesMean (actualUnusedPool c full) centralPoolValue
  let free : ℝ := ∑ z ∈ columnCells j \ full, ((entry c z : ℝ) - ν)
  have hp := (fixed_reservation_same_unused_pool a c full hfixed).2
  have hf := fixed_reservation_free_line_residual a c full (columnCells j)
    (centralEntriesMean (actualUnusedPool a full) centralPoolValue) hfixed
  rw [← columnSum_real_cells c j] at hf
  have hfree : |free| < (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n := by
    dsimp [free, ν]
    rw [hp, ← hf]
    exact hcompletion
  have hcmp : |(columnSum reference j : ℝ) - ((n : ℝ) * μ + free)| ≤ K := hcomparison
  have htriangle := abs_add_le ((columnSum reference j : ℝ) - ((n : ℝ) * μ + free)) free
  have hid : (columnSum reference j : ℝ) - (n : ℝ) * μ =
      ((columnSum reference j : ℝ) - ((n : ℝ) * μ + free)) + free := by ring
  rw [hid]
  linarith

end
end Sude
