import PASoundness.PAtoCompactConditionalTransitivityOrderFirst
import PASoundness.PAtoCompactConditionalTransitivityOrderSecond
import PASoundness.PAtoCompactConditionalTransitivityOrderGuard

/-! Guarded order composition from the two actual quantified K order clauses.
The domain memberships and all four edges are explicit assumptions; no
composite graph or full order transfer is constructed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityOrderInstance
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityOrderFirst
open PASoundness.PAtoCompactConditionalTransitivityOrderSecond
open PASoundness.PAtoCompactConditionalTransitivityOrderGuard
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Both literal order clauses yield pointwise order agreement for the
displayed endpoints and middle points, provided their full guards hold. -/
def guarded_order_from_clauses : KDerivation
    (imp orderFormula.encode (imp secondOrder.encode
      (imp (both firstGuard secondGuard)
        (sameOrder (member 4 2) (member 5 3))))) := by
  let Γ := [both firstGuard secondGuard, secondOrder.encode, orderFormula.encode]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have ho : Context Γ orderFormula.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ secondOrder.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ (both firstGuard secondGuard) := Context.head _ _
  have hp : Context Γ firstPoint := by
    have hh := Context.mp ho (.closed first_order_instance)
    simpa only [first_matrix_code, firstPoint, firstGuard, sameOrder] using hh
  have hq : Context Γ secondPoint := by
    have hh := Context.mp hs (.closed second_order_instance)
    simpa only [second_guarded_code, secondPoint, secondGuard, sameOrder] using hh
  exact .mp hg (.mp hq (.mp hp (.closed guarded_order_point)))

theorem guarded_order_from_clauses_certificate :
    theoremCode (certificate guarded_order_from_clauses) =
      imp orderFormula.encode (imp secondOrder.encode
        (imp (both firstGuard secondGuard)
          (sameOrder (member 4 2) (member 5 3)))) :=
  certificate_correct guarded_order_from_clauses

end PASoundness.PAtoCompactConditionalTransitivityOrderInstance

#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderInstance.guarded_order_from_clauses
#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderInstance.guarded_order_from_clauses_certificate
