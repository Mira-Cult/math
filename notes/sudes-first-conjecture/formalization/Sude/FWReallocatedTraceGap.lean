import Sude.FWPhysicalEdgeTraceGrid

/-! Recover the same physical seed/growth gap function after reallocation.
Preserved growth entries and gap-two seed pairs suffice; individual seed
values may move. No orientation or invoice is inferred from subtraction alone. -/
namespace Sude
noncomputable section

/-- Preserving both growth endpoints and preserving gap two on each seed pair
preserves the entire physical trace-gap function. -/
theorem fw_reallocated_physical_trace_gap_eq {n P : ℕ}
    (grown b : Cell n ≃ Fin (n*n))
    (seedCells : Fin 16 → Bool → Cell n) (growthCells : Fin P → Bool → Cell n)
    (hseedOld : ∀ j, entry grown (seedCells j true) = entry grown (seedCells j false) + 2)
    (hseedNew : ∀ j, entry b (seedCells j true) = entry b (seedCells j false) + 2)
    (hgrowth : ∀ j side, entry b (growthCells j side) = entry grown (growthCells j side)) :
    fwPhysicalEdgeTraceGap b seedCells growthCells = fwPhysicalEdgeTraceGap grown seedCells growthCells := by
  funext x
  cases x with
  | inl j =>
    simp only [fwPhysicalEdgeTraceGap]
    have ho := hseedOld j
    have hn := hseedNew j
    omega
  | inr j =>
    simp only [fwPhysicalEdgeTraceGap, hgrowth]

/-- An existing physical trace grid transfers to the reallocated square under
the same supplied gap and endpoint equalities. -/
theorem fw_reallocated_physical_trace_grid {n P : ℕ}
    (grown b : Cell n ≃ Fin (n*n))
    (seedCells : Fin 16 → Bool → Cell n) (growthCells : Fin P → Bool → Cell n)
    (hseedOld : ∀ j, entry grown (seedCells j true) = entry grown (seedCells j false) + 2)
    (hseedNew : ∀ j, entry b (seedCells j true) = entry b (seedCells j false) + 2)
    (hgrowth : ∀ j side, entry b (growthCells j side) = entry grown (growthCells j side))
    (S : Finset (Sum (Fin 16) (Fin P))) (R : ℕ)
    (hgrid : CompleteEvenGrid S (fwPhysicalEdgeTraceGap grown seedCells growthCells) R) :
    CompleteEvenGrid S (fwPhysicalEdgeTraceGap b seedCells growthCells) R := by
  rw [fw_reallocated_physical_trace_gap_eq grown b seedCells growthCells hseedOld hseedNew hgrowth]
  exact hgrid

end
end Sude
