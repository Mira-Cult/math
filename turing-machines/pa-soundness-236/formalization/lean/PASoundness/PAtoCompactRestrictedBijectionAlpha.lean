import PASoundness.PAtoCompactRestrictedForwardAlpha
import PASoundness.PAtoCompactRestrictedBackwardAlpha

/-! Binder preparation for the exact bijection clause before changing its
free source, target, and graph names. No substitution stability for arbitrary
K proofs and no quotient theorem is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedBijectionAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactRestrictedForwardAlpha PASoundness.PAtoCompactRestrictedBackwardAlpha
open PASoundness.PAtoCompactBijectionBackwardAtThree
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

/-- Original bijection with source-coordinate binders changed from 2 to 7,
while source 0, target 1 and graph 6 remain unchanged. -/
def alphaBijection : Formula := conj preparedForward alphaClause

private def backward_equiv : ProofEquiv originalClause alphaClause := by
  have h := ProofEquiv.universal 3
    (ProofEquiv.implication (ProofEquiv.refl (.member 1 3))
      (ProofEquiv.alphaExists 2 7 (witness 2) (by decide) (by decide) (by decide)))
  have hs : replace 2 7 (witness 2) = witness 7 := by decide
  rw [hs] at h
  simpa only [originalClause, alphaClause] using h

private def conj_equiv {a a' b b' : Formula} (ha : ProofEquiv a a')
    (hb : ProofEquiv b b') : ProofEquiv (conj a b) (conj a' b') := by
  have hn := ProofEquiv.implication hb (ProofEquiv.refl .bottom)
  have hi := ProofEquiv.implication ha hn
  exact ProofEquiv.implication hi (ProofEquiv.refl .bottom)

/-- Exact K proof equivalence: alpha-convert the forward input binder and
reverse preimage binder separately, preserving shared graph and endpoints.
No object inequality, graph construction, or quotient law is assumed. -/
def bijection_alpha : ProofEquiv bijectionFormula alphaBijection := by
  have h := conj_equiv prepare_alpha backward_equiv
  change ProofEquiv bijectionFormula alphaBijection at h
  exact h

theorem bijection_alpha_forward_certificate :
    theoremCode (certificate bijection_alpha.forward) =
      imp bijectionFormula.encode alphaBijection.encode := certificate_correct bijection_alpha.forward

theorem bijection_alpha_backward_certificate :
    theoremCode (certificate bijection_alpha.backward) =
      imp alphaBijection.encode bijectionFormula.encode := certificate_correct bijection_alpha.backward

end PASoundness.PAtoCompactRestrictedBijectionAlpha

#print axioms PASoundness.PAtoCompactRestrictedBijectionAlpha.bijection_alpha
#print axioms PASoundness.PAtoCompactRestrictedBijectionAlpha.bijection_alpha_forward_certificate
#print axioms PASoundness.PAtoCompactRestrictedBijectionAlpha.bijection_alpha_backward_certificate
