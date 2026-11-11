import Sude.FWReallocatedTraceGap
import Sude.BridgeChosenGrid

/-! Transfer the supplied seed/growth, bridge and wide grid labels after a
seed-only reallocation. No physical orientation or flow is asserted. -/
namespace Sude
noncomputable section

/-- Existing joined grids retain their same labels and radius when both seed
squares have gap two and each growth endpoint is unchanged. The bridge and
wide gap functions are supplied unchanged. -/
theorem fw_reallocated_joined_grid {n P J : ℕ}
    (grown b : Cell n ≃ Fin (n*n))
    (seedCells : Fin 16 → Bool → Cell n) (growthCells : Fin P → Bool → Cell n)
    (hseedOld : ∀ j, entry grown (seedCells j true) = entry grown (seedCells j false) + 2)
    (hseedNew : ∀ j, entry b (seedCells j true) = entry b (seedCells j false) + 2)
    (hgrowth : ∀ j side, entry b (growthCells j side) = entry grown (growthCells j side))
    (batches : ℕ → List DoublePair) (index : ℕ) (wide : Fin J → ℕ)
    (S : Finset (((Fin 16 ⊕ Fin P) ⊕ ℕ) ⊕ Fin J)) (R : ℕ)
    (hgrid : CompleteEvenGrid S
      (Sum.elim (joinedBridgeGap (fwPhysicalEdgeTraceGap grown seedCells growthCells) batches index) wide) R) :
    CompleteEvenGrid S
      (Sum.elim (joinedBridgeGap (fwPhysicalEdgeTraceGap b seedCells growthCells) batches index) wide) R := by
  rw [fw_reallocated_physical_trace_gap_eq grown b seedCells growthCells hseedOld hseedNew hgrowth]
  exact hgrid

end
end Sude
