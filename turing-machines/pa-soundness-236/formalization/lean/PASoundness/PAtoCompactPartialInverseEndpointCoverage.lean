import PASoundness.PAtoCompactPartialInverseNewEdge
import PASoundness.PAtoCompactPartialInverseEndpoint
import PASoundness.PAtoCompactPartialInverseImageFunction

/-! One new-endpoint coverage instance from supplied image, pair, adjunction,
source equality and old edge. It is conditional, retains the point and image
witnesses, and does not establish the old-prefix case or no-spurious edges. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseEndpointCoverage
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactPartialInverseNewEdge PASoundness.PAtoCompactPartialInverseEndpoint
open PASoundness.PAtoCompactPartialInverseImageWitness PASoundness.PAtoCompactPartialInverseImageFunction
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- At a queried source equal to endpoint 12, supplied bijection image 13,
its inverse pair at point 11, and a graph adjoining that point supply the
reverse edge for any old target-domain edge from the queried source. -/
def endpoint_coverage : KDerivation
    (imp (adjoinCode 7 11 9 14)
      (imp (pairFormula 11 13 12).encode
        (imp imageWitness (imp (member 1 3) (imp (equal 12 2)
          (imp (graphFormula 6 2 3).encode (graphFormula 9 3 2).encode)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let A := adjoinCode 7 11 9 14
  let P := (pairFormula 11 13 12).encode
  let E := (graphFormula 6 2 3).encode
  let Γ := [E,equal 12 2,member 1 3,imageWitness,P,A]
  have hg : Context Γ E := Context.head _ _
  have he : Context Γ (equal 12 2) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 1 3) := .hypothesis (by simp [Γ])
  have hw : Context Γ imageWitness := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hnew : Context Γ (graphFormula 9 13 12).encode :=
    .mp hp (.mp ha (.closed adjoin_new_inverse_edge))
  have htarget : Context Γ (equal 13 3) :=
    .mp hg (.mp he (.mp hm (.mp hw (.closed image_witness_functional))))
  exact .mp hnew (.mp he (.mp htarget (.closed transport_endpoint_edge)))

theorem endpoint_coverage_certificate : theoremCode (certificate endpoint_coverage) =
    imp (adjoinCode 7 11 9 14)
      (imp (pairFormula 11 13 12).encode
        (imp imageWitness (imp (member 1 3) (imp (equal 12 2)
          (imp (graphFormula 6 2 3).encode (graphFormula 9 3 2).encode))))) :=
  certificate_correct endpoint_coverage

end PASoundness.PAtoCompactPartialInverseEndpointCoverage

#print axioms PASoundness.PAtoCompactPartialInverseEndpointCoverage.endpoint_coverage
#print axioms PASoundness.PAtoCompactPartialInverseEndpointCoverage.endpoint_coverage_certificate
