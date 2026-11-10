import PASoundness.PAtoCompactOrderIsomorphism

/-! Capture-safe reversal of the two designated input names in the concrete
order-isomorphism candidate. This is syntactic and standard-semantic setup:
it does not prove K symmetry or construct an inverse graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOrderIsoSwap
open PASoundness.CompactNamed PASoundness.CompactMatrix
open PASoundness.PAtoCompactOrderIsomorphism

/-- Simultaneously swap the free names 0 and 1 using fresh intermediate name 8. -/
def reverseEquivalent : CompactNamed.Formula :=
  replace 8 1 (replace 1 0 (replace 0 8 equivalentFormula))

/-- The graph binder and all pair-witness binders remain bound after the swap. -/
theorem reverse_free : reverseEquivalent.free = {0,1} := by decide

theorem spare_fresh : 8 ∉ equivalentFormula.names := by decide

/-- The environment that swaps exactly the interpretations of names 0 and 1. -/
def swapAssignment (ρ : Environment) : Environment :=
  update (update ρ 0 (ρ 1)) 1 (ρ 0)

/-- The syntactic reversal reads the same as swapping the two input values in
standard HF semantics. This is independent of K/PA soundness. -/
theorem reverse_realize (ρ : Environment) :
    reverseEquivalent.Realize ρ ↔ equivalentFormula.Realize (swapAssignment ρ) := by
  unfold reverseEquivalent
  rw [replace_realize 8 1 _ (by decide) (by decide)]
  rw [replace_realize 1 0 _ (by decide) (by decide)]
  rw [replace_realize 0 8 _ (by decide) (by decide)]
  apply CompactNamed.Formula.realize_agree
  intro v hv
  have h8 : v ≠ 8 := fun he => spare_fresh (he ▸ hv)
  by_cases h0 : v = 0 <;> by_cases h1 : v = 1 <;>
    simp [update, swapAssignment, h8, h0, h1]

/-- The same comparison for the actual encoded K conclusion. -/
theorem reverse_encoded_realize (ρ : Environment) :
    (decode reverseEquivalent.encode).Realize ρ ↔
      (decode equivalentFormula.encode).Realize (swapAssignment ρ) := by
  rw [CompactNamed.Formula.encode_realize, CompactNamed.Formula.encode_realize]
  exact reverse_realize ρ

end PASoundness.PAtoCompactOrderIsoSwap

#print axioms PASoundness.PAtoCompactOrderIsoSwap.reverse_realize
#print axioms PASoundness.PAtoCompactOrderIsoSwap.reverse_encoded_realize
