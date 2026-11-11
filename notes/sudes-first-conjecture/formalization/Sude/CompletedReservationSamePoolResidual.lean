import Sude.RFReferenceFreeResidual
import Sude.ActualUnusedRoleImageTransport

/-! Same-geometric-reservation unused-pool transport across a completion.
All completion and line estimates are supplied. This does not infer a DQ/RF
analytic gate or identify a different enlarged diagonal reservation. -/
namespace Sude
noncomputable section

/-- If the completion fixes every entry on this exact reservation, its actual
unused pool and its central mean are unchanged. -/
theorem fixed_reservation_same_unused_pool {n : ℕ}
    (a c : Cell n ≃ Fin (n*n)) (full : Finset (Cell n))
    (hfixed : ∀ z ∈ full, entry c z = entry a z) :
    actualUnusedPool c full = actualUnusedPool a full ∧
      centralEntriesMean (actualUnusedPool c full) centralPoolValue =
        centralEntriesMean (actualUnusedPool a full) centralPoolValue := by
  classical
  have himage : full.image (entry c) = full.image (entry a) := by
    apply Finset.image_congr
    intro z hz
    exact hfixed z hz
  have hp := actualUnusedPool_eq_of_role_value_image_eq c a full himage
  exact ⟨hp, by rw [hp]⟩

/-- The supplied DQ/RF completion estimates bound free cells relative to the
literal unused mean of the same completed square and geometric reservation. -/
theorem dq_rf_completed_same_pool_free_residual {n bits : ℕ}
    (a c : Cell n ≃ Fin (n*n)) (full : Finset (Cell n)) (ε : ℝ)
    (hfixed : ∀ z ∈ full, entry c z = entry a z)
    (hrow : ∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry a z : ℝ)) +
        ((rowCells i \ full).card : ℝ) * centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)
    (hcol : ∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry a z : ℝ)) +
        ((columnCells i \ full).card : ℝ) * centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) :
    (∀ i, |∑ z ∈ rowCells i \ full, ((entry c z : ℝ) -
        centralEntriesMean (actualUnusedPool c full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
    (∀ i, |∑ z ∈ columnCells i \ full, ((entry c z : ℝ) -
        centralEntriesMean (actualUnusedPool c full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) := by
  have hp := (fixed_reservation_same_unused_pool a c full hfixed).1
  rw [hp]
  exact dq_rf_completion_free_residual a c full ε hfixed hrow hcol

/-- The same free-cell bounds transfer to a supplied synchronized reference
that agrees with the completed square outside an active subset of the same
geometric reservation. No other reference or flow property is asserted. -/
theorem dq_rf_reference_same_completed_pool_free_residual {n bits : ℕ}
    (a c d : Cell n ≃ Fin (n*n)) (active full : Finset (Cell n)) (ε : ℝ)
    (hsub : active ⊆ full)
    (hcfix : ∀ z ∈ full, entry c z = entry a z)
    (hdfix : ∀ z ∉ active, entry d z = entry c z)
    (hrow : ∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry a z : ℝ)) +
        ((rowCells i \ full).card : ℝ) * centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n)
    (hcol : ∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry a z : ℝ)) +
        ((columnCells i \ full).card : ℝ) * centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) :
    (∀ i, |∑ z ∈ rowCells i \ full, ((entry d z : ℝ) -
        centralEntriesMean (actualUnusedPool c full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) ∧
    (∀ i, |∑ z ∈ columnCells i \ full, ((entry d z : ℝ) -
        centralEntriesMean (actualUnusedPool c full) centralPoolValue)| <
          (1 + 2 * (9*bits+6 : ℕ) * ε) * poolMaximum n + 3 * poolMaximum n) := by
  have hp := (fixed_reservation_same_unused_pool a c full hcfix).1
  rw [hp]
  exact dq_rf_reference_free_residual a c d active full ε hsub hcfix hdfix hrow hcol

end
end Sude
