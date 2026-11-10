import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactQuantifiers

/-! Instantiation of the second guarded order clause in a proposed
composition of two represented isomorphisms. This does not construct a
composite graph or establish transitivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityOrderSecond
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not
private def iff' (a b : Formula) : Formula := conj (a.imp b) (b.imp a)

/-- The second isomorphism's order clause. Input names 0,1,6 of the
original clause are moved to 1,8,7, respectively. -/
def secondOrder : Formula :=
  replace 6 7 (replace 0 1 (replace 1 8 orderFormula))

private def secondBody : Formula := .imp
  (conj (.member 1 2) (conj (.member 1 4) (conj (.member 8 3)
    (conj (.member 8 5) (conj (graphFormula 7 2 3) (graphFormula 7 4 5))))))
  (iff' (.member 4 2) (.member 5 3))

private def pointBody : Formula := .imp
  (conj (.member 1 10) (conj (.member 1 11) (conj (.member 8 3)
    (conj (.member 8 5) (conj (graphFormula 7 10 3) (graphFormula 7 11 5))))))
  (iff' (.member 11 10) (.member 5 3))

/-- Exact guarded target, with both middle-domain, both target-domain,
and both second-graph edges explicit. -/
def secondGuarded : Nat := pointBody.encode

theorem second_guarded_code : secondGuarded =
    imp (both (member 1 10) (both (member 1 11) (both (member 8 3)
      (both (member 8 5) (both (graphFormula 7 10 3).encode (graphFormula 7 11 5).encode)))))
      (both (imp (member 11 10) (member 5 3)) (imp (member 5 3) (member 11 10))) := rfl

private theorem second_order_syntax : secondOrder =
    .all 2 (.all 4 (.all 3 (.all 5 secondBody))) := by decide

private theorem first_replacement :
    replace 2 10 (.all 4 (.all 3 (.all 5 secondBody))) =
      .all 4 (.all 3 (.all 5 (replace 2 10 secondBody))) := by decide

private theorem second_replacement :
    replace 4 11 (.all 3 (.all 5 (replace 2 10 secondBody))) =
      .all 3 (.all 5 pointBody) := by decide

/-- The literal second order clause yields the desired guarded pointwise
comparison; no edge outside the displayed domains is used. -/
def second_order_instance : KDerivation (imp secondOrder.encode secondGuarded) := by
  have h2 := universalInstance 2 10 (.all 4 (.all 3 (.all 5 secondBody)))
    (by decide) (by decide) (by decide)
  rw [first_replacement] at h2
  have h4 := universalInstance 4 11 (.all 3 (.all 5 (replace 2 10 secondBody)))
    (by decide) (by decide) (by decide)
  rw [second_replacement] at h4
  have h3 := allSpecialize 3 (.all 5 pointBody) (by decide)
  have h5 := allSpecialize 5 pointBody (by decide)
  have hs := compose h2 (compose h4 (compose h3 h5))
  simpa only [second_order_syntax, secondGuarded, Formula.encode] using hs

theorem second_order_instance_certificate :
    theoremCode (certificate second_order_instance) =
      imp secondOrder.encode secondGuarded := certificate_correct second_order_instance

end PASoundness.PAtoCompactConditionalTransitivityOrderSecond

#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderSecond.second_order_instance
#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderSecond.second_order_instance_certificate
