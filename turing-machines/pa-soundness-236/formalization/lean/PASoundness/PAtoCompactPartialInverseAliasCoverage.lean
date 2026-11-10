import PASoundness.PAtoCompactPartialInverseEndpointCoverage

/-! Reconnect the image endpoint alias to the actual old-prefix name. This
local K result assumes both equalities explicitly and does not establish the
successor graph, whole case split, or partial-inverse induction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseAliasCoverage
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactPartialInverseImageWitness PASoundness.PAtoCompactPartialInverseEndpointCoverage
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- When endpoint alias 12 equals prefix 8 and the queried source 2 equals
prefix 8, the supplied endpoint witnesses give the queried inverse edge. -/
def alias_endpoint_coverage : KDerivation
    (imp (adjoinCode 7 11 9 14) (imp (pairFormula 11 13 12).encode
      (imp imageWitness (imp (member 1 3) (imp (equal 12 8) (imp (equal 8 2)
        (imp (graphFormula 6 2 3).encode (graphFormula 9 3 2).encode))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let A := adjoinCode 7 11 9 14
  let P := (pairFormula 11 13 12).encode
  let E := (graphFormula 6 2 3).encode
  let Γ := [E,equal 8 2,equal 12 8,member 1 3,imageWitness,P,A]
  have hg : Context Γ E := Context.head _ _
  have h82 : Context Γ (equal 8 2) := .hypothesis (by simp [Γ])
  have h128 : Context Γ (equal 12 8) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 1 3) := .hypothesis (by simp [Γ])
  have hw : Context Γ imageWitness := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have h122 : Context Γ (equal 12 2) := Context.eqTrans h128 h82
  exact .mp hg (.mp h122 (.mp hm (.mp hw (.mp hp (.mp ha (.closed endpoint_coverage))))))

theorem alias_endpoint_coverage_certificate :
    theoremCode (certificate alias_endpoint_coverage) =
      imp (adjoinCode 7 11 9 14) (imp (pairFormula 11 13 12).encode
        (imp imageWitness (imp (member 1 3) (imp (equal 12 8) (imp (equal 8 2)
          (imp (graphFormula 6 2 3).encode (graphFormula 9 3 2).encode)))))) :=
  certificate_correct alias_endpoint_coverage

end PASoundness.PAtoCompactPartialInverseAliasCoverage

#print axioms PASoundness.PAtoCompactPartialInverseAliasCoverage.alias_endpoint_coverage
#print axioms PASoundness.PAtoCompactPartialInverseAliasCoverage.alias_endpoint_coverage_certificate
