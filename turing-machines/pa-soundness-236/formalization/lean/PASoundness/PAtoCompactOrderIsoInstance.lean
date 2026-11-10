import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactQuantifiers

/-! Instantiation of the exact candidate's four universally quantified order
coordinates at their own names. The quantifier elimination is constructed in
K via the existing fresh-alpha-conversion rule; this is not a semantic
soundness argument or an order-isomorphism construction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOrderIsoInstance
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact matrix of the candidate's order clause, after its four
quantifiers. It contains the candidate's domain guards and graph formulas. -/
def orderMatrix : Formula := match orderFormula with
  | .all _ (.all _ (.all _ (.all _ f))) => f
  | _ => .truth

/-- The exact quantified order code entails its pointwise matrix, with no
premise about existence of an inverse graph. -/
def order_instance : KDerivation (imp orderFormula.encode orderMatrix.encode) := by
  have h₂ := allSpecialize 2 (.all 4 (.all 3 (.all 5 orderMatrix))) (by decide)
  have h₄ := allSpecialize 4 (.all 3 (.all 5 orderMatrix)) (by decide)
  have h₃ := allSpecialize 3 (.all 5 orderMatrix) (by decide)
  have h₅ := allSpecialize 5 orderMatrix (by decide)
  exact compose h₂ (compose h₄ (compose h₃ h₅))

theorem order_instance_certificate :
    theoremCode (certificate order_instance) = imp orderFormula.encode orderMatrix.encode :=
  certificate_correct order_instance

end PASoundness.PAtoCompactOrderIsoInstance

#print axioms PASoundness.PAtoCompactOrderIsoInstance.order_instance
#print axioms PASoundness.PAtoCompactOrderIsoInstance.order_instance_certificate
