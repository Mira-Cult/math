import PASoundness.PAtoCompactOrderIsomorphism

/-! Exact target-order syntax for the conditional composition argument.
No proof of the target order, graph existence, or transitivity is claimed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityOrderTargetSyntax
open PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism

private def conj (a b : Formula) : Formula := (a.imp b.not).not

/-- The original candidate order with its target and graph names changed. -/
def targetOrder : Formula := replace 6 9 (replace 1 8 orderFormula)

/-- Exact four-domain/two-edge guard, as a named formula. -/
def targetGuardFormula : Formula :=
  conj (.member 0 2) (conj (.member 0 4)
    (conj (.member 8 3) (conj (.member 8 5)
      (conj (graphFormula 9 2 3) (graphFormula 9 4 5)))))

/-- Encoded guard used by K contexts. -/
def targetGuard : Nat := targetGuardFormula.encode

/-- Its pointwise guarded order preservation and reflection. -/
def targetPoint : Formula := .imp targetGuardFormula
  (conj (.imp (.member 4 2) (.member 5 3))
    (.imp (.member 5 3) (.member 4 2)))

/-- The renamed target has exactly this quantified body. -/
theorem target_order_syntax : targetOrder = .all 2 (.all 4 (.all 3 (.all 5 targetPoint))) := by
  rfl

end PASoundness.PAtoCompactConditionalTransitivityOrderTargetSyntax

#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderTargetSyntax.target_order_syntax
