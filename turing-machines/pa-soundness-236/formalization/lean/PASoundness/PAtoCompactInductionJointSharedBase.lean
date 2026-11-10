import PASoundness.PAtoCompactInductionJointHighAllocation

/-! The joint zero-base allocation also covers the augmented guard needed by
the qfree successor step; no separate graph base is necessary. -/
namespace PASoundness.PAtoCompactInductionJointSharedBase
open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactInductionAugmentedGuard
open PASoundness.PAtoCompactInductionJointLowAllocation PASoundness.PAtoCompactInductionJointHighAllocation

/-- Under the common allocation, the guard for the source together with the
fresh predecessor variable fits in the same zero-graph base. -/
theorem augmented_guard_le_highBase (φ : Peano.Formula) (x : Nat) :
    guardBase (augmented (Peano.inductionAxiom φ x) (lowBound φ x+1)) ≤ highBase φ x := by
  have h := high_allocation φ x
  dsimp only at h
  have hb : lowBound φ x + 101 < highBase φ x := h.1
  have hg : guardBase (Peano.inductionAxiom φ x) ≤ highBase φ x := h.2.2.1
  simp only [guardBase, augmented_free, Finset.sup_union, Finset.sup_singleton, id_eq] at hg ⊢
  omega
end PASoundness.PAtoCompactInductionJointSharedBase

#print axioms PASoundness.PAtoCompactInductionJointSharedBase.augmented_guard_le_highBase
