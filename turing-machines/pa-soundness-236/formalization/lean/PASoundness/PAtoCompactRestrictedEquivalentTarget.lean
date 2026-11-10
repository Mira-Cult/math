import PASoundness.PAtoCompactRestrictedBijectionAlpha
import PASoundness.PAtoCompactRestrictedOuterAlpha
import PASoundness.PAtoCompactRestrictedMatrix

/-! Capture-safe target syntax for the restricted-graph isomorphism.
The alpha conversions are actual K proof equivalences before changing free
endpoint names. Free replacement itself is only a syntax operation here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedEquivalentTarget
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactRestrictedBijectionAlpha
open PASoundness.PAtoCompactRestrictedForwardAlpha PASoundness.PAtoCompactRestrictedBackwardAlpha
open PASoundness.PAtoCompactRestrictedOrderAlpha PASoundness.PAtoCompactRestrictedOuterAlpha
open PASoundness.PAtoCompactRestrictedMatrix
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

private def conj_equiv {a a' b b' : Formula} (ha : ProofEquiv a a')
    (hb : ProofEquiv b b') : ProofEquiv (conj a b) (conj a' b') := by
  have hn := ProofEquiv.implication hb (ProofEquiv.refl .bottom)
  have hi := ProofEquiv.implication ha hn
  exact ProofEquiv.implication hi (ProofEquiv.refl .bottom)

/-- The literal canonical formula with all conflicting coordinate binders
and the graph binder changed, but its original free endpoints 0,1 retained. -/
def preparedEquivalent : Formula := .ex 8 (replace 6 8 alphaMatrix)

/-- The preparation is justified by actual bidirectional finite K proofs:
first alpha-convert both bijection clauses and order coordinates under ∃6,
then convert the graph witness ∃6 to ∃8. -/
def prepare_equivalent : ProofEquiv equivalentFormula preparedEquivalent := by
  have hm : ProofEquiv (conj bijectionFormula orderFormula) alphaMatrix := by
    have h := conj_equiv bijection_alpha order_alpha
    change ProofEquiv (conj bijectionFormula orderFormula) alphaMatrix at h
    exact h
  have hx := ProofEquiv.existential 6 hm
  have h := hx.trans graph_alpha
  change ProofEquiv equivalentFormula preparedEquivalent at h
  exact h

/-- Endpoint names are replaced only after the binders have been prepared;
the graph witness is already bound at 8. This definition records the exact
literal target and does not by itself transport a K proof through replacement. -/
def endpointTarget : Formula := replace 1 5 (replace 0 2 preparedEquivalent)

private def namedTarget : Formula := .ex 8
  (conj (conj restrictedForward restrictedClause) renamedOrder)

/-- Syntactically, the safe endpoint instance is exactly the independently
constructed restricted bijection and order clauses with the same graph 8. -/
theorem endpoint_target_syntax : endpointTarget = namedTarget := by decide

/-- The literal numeric target is exactly the existential restricted matrix
already derived under the supplied graph-filter hypotheses. -/
theorem endpoint_target_code : endpointTarget.encode = existsCode 8 restrictedMatrix := by
  rw [endpoint_target_syntax]
  simp only [namedTarget, conj, Formula.not, Formula.encode, CompactProof.both,
    CompactProof.neg, restricted_forward_code, restricted_clause_code, renamed_order_code,
    restrictedMatrix, forwardClause, backwardClause]

/-- Both K identity directions for the exact numeric target. -/
def target_to_restricted : KDerivation (imp endpointTarget.encode (existsCode 8 restrictedMatrix)) := by
  rw [← endpoint_target_code]
  exact CompactHilbertBasis.identity _

def restricted_to_target : KDerivation (imp (existsCode 8 restrictedMatrix) endpointTarget.encode) := by
  rw [← endpoint_target_code]
  exact CompactHilbertBasis.identity _

end PASoundness.PAtoCompactRestrictedEquivalentTarget

#print axioms PASoundness.PAtoCompactRestrictedEquivalentTarget.prepare_equivalent
#print axioms PASoundness.PAtoCompactRestrictedEquivalentTarget.endpoint_target_code
#print axioms PASoundness.PAtoCompactRestrictedEquivalentTarget.target_to_restricted
#print axioms PASoundness.PAtoCompactRestrictedEquivalentTarget.restricted_to_target
