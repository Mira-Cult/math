import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactDerivations

/-! Capture-safe equality transport for one newly adjoined inverse edge.
The equalities and edge are explicit antecedents; no witness uniqueness or
full partial-inverse successor step is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseEndpoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The supplied image and source equalities transport a new edge from fixed
endpoint names 13,12 to the queried coordinates 3,2. Graph binder names
19–22 are fresh for all four coordinates and graph name 9. -/
def transport_endpoint_edge : KDerivation
    (imp (equal 13 3) (imp (equal 12 2)
      (imp (graphFormula 9 13 12).encode (graphFormula 9 3 2).encode))) := by
  have ha := (equalityReplace 13 3 (graphFormula 9 13 12) (by decide) (by decide)).1
  have hb := (equalityReplace 12 2 (graphFormula 9 3 12) (by decide) (by decide)).1
  have hrenameA : replace 13 3 (graphFormula 9 13 12) = graphFormula 9 3 12 := by decide
  have hrenameB : replace 12 2 (graphFormula 9 3 12) = graphFormula 9 3 2 := by decide
  rw [hrenameA] at ha
  rw [hrenameB] at hb
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 9 13 12).encode,equal 12 2,equal 13 3]
  have he : Context Γ (graphFormula 9 13 12).encode := Context.head _ _
  have ha' : Context Γ (equal 13 3) := .hypothesis (by simp [Γ])
  have hb' : Context Γ (equal 12 2) := .hypothesis (by simp [Γ])
  exact .mp (.mp he (.mp ha' (.closed ha))) (.mp hb' (.closed hb))

theorem transport_endpoint_edge_certificate :
    theoremCode (certificate transport_endpoint_edge) =
      imp (equal 13 3) (imp (equal 12 2)
        (imp (graphFormula 9 13 12).encode (graphFormula 9 3 2).encode)) :=
  certificate_correct transport_endpoint_edge

end PASoundness.PAtoCompactPartialInverseEndpoint

#print axioms PASoundness.PAtoCompactPartialInverseEndpoint.transport_endpoint_edge
#print axioms PASoundness.PAtoCompactPartialInverseEndpoint.transport_endpoint_edge_certificate
