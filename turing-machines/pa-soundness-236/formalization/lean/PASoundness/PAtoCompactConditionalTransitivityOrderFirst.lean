import PASoundness.PAtoCompactOrderIsoInstance

/-! Capture-safe instantiation of the first literal order clause for two
explicit source and middle points. The guard retains both domains and both
graph edges; no graph composition or transitivity is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityOrderFirst
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInstance
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Instantiate the two middle coordinates at fresh names 10 and 11. -/
def firstMatrix : Formula := replace 5 11 (replace 3 10 orderMatrix)

/-- Its literal guard and order conclusion, with no omitted domain guards. -/
theorem first_matrix_code : firstMatrix.encode =
    imp (both (member 0 2) (both (member 0 4)
      (both (member 1 10) (both (member 1 11)
        (both (graphFormula 6 2 10).encode (graphFormula 6 4 11).encode)))))
      (both (imp (member 4 2) (member 11 10)) (imp (member 11 10) (member 4 2))) := by
  rfl

/-- The quantified source order formula yields the displayed instance in K. -/
def first_order_instance : KDerivation (imp orderFormula.encode firstMatrix.encode) := by
  have h₂ := allSpecialize 2 (.all 4 (.all 3 (.all 5 orderMatrix))) (by decide)
  have h₄ := allSpecialize 4 (.all 3 (.all 5 orderMatrix)) (by decide)
  have h₃ := universalInstance 3 10 (.all 5 orderMatrix) (by decide) (by decide) (by decide)
  have h₃' : KDerivation (imp (allCode 3 (Formula.all 5 orderMatrix).encode)
      (allCode 5 (replace 3 10 orderMatrix).encode)) := by
    have hs : replace 3 10 (.all 5 orderMatrix) = .all 5 (replace 3 10 orderMatrix) := by decide
    rw [hs] at h₃
    exact h₃
  have h₅ := universalInstance 5 11 (replace 3 10 orderMatrix) (by decide) (by decide) (by decide)
  exact compose h₂ (compose h₄ (compose h₃' h₅))

theorem first_order_instance_certificate :
    theoremCode (certificate first_order_instance) = imp orderFormula.encode firstMatrix.encode :=
  certificate_correct first_order_instance

end PASoundness.PAtoCompactConditionalTransitivityOrderFirst

#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderFirst.first_order_instance
#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderFirst.first_order_instance_certificate
