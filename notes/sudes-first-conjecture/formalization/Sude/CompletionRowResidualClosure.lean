import Sude.CompletedReservationSamePoolResidual

/-! Close a supplied same-completion row residual estimate using its explicit
DQ/RF completion bound. This does not construct a completion or prove a final
numerical threshold, primality, or any later-flow property. -/
namespace Sude
noncomputable section

/-- The completed square fixes this exact reservation, so the DQ/RF row
estimate bounds the free residual around the completed square's unused mean.
One supplied midpoint residual comparison then gives the displayed strict row
bound for the same reference. All witness and analytic inputs remain explicit. -/
theorem completion_row_residual_closure {n bits : ℕ}
    (a c reference : Cell n ≃ Fin (n*n)) (full : Finset (Cell n))
    (r : Fin n) (ε μ K : ℝ)
    (hfixed : ∀ z ∈ full, entry c z = entry a z)
    (hcompletion : |(rowSum c r : ℝ) - ((∑ z ∈ rowCells r ∩ full, (entry a z : ℝ)) +
        ((rowCells r \ full).card : ℝ) * centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)
    (hcomparison : |(rowSum reference r : ℝ) - ((n : ℝ) * μ +
        ∑ z ∈ rowCells r \ full, ((entry c z : ℝ) -
          centralEntriesMean (actualUnusedPool c full) centralPoolValue))| ≤ K) :
    |(rowSum reference r : ℝ) - (n : ℝ) * μ| <
      K + ((1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) := by
  classical
  let ν := centralEntriesMean (actualUnusedPool c full) centralPoolValue
  let free : ℝ := ∑ z ∈ rowCells r \ full, ((entry c z : ℝ) - ν)
  have hp := (fixed_reservation_same_unused_pool a c full hfixed).2
  have hf := fixed_reservation_free_line_residual a c full (rowCells r)
    (centralEntriesMean (actualUnusedPool a full) centralPoolValue) hfixed
  rw [← rowSum_real_cells c r] at hf
  have hfree : |free| < (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n := by
    dsimp [free, ν]
    rw [hp, ← hf]
    exact hcompletion
  have hcmp : |(rowSum reference r : ℝ) - ((n : ℝ) * μ + free)| ≤ K := hcomparison
  have htriangle := abs_add_le ((rowSum reference r : ℝ) - ((n : ℝ) * μ + free)) free
  have hid : (rowSum reference r : ℝ) - (n : ℝ) * μ =
      ((rowSum reference r : ℝ) - ((n : ℝ) * μ + free)) + free := by ring
  rw [hid]
  linarith

end
end Sude
