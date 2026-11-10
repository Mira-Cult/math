import PASoundness.PAtoCompactRestrictedForwardAlpha
import PASoundness.PAtoCompactRestrictedBackwardAlpha
import PASoundness.PAtoCompactRestrictedOrderAlpha

/-! The outer graph binder of the prepared candidate order-isomorphism
formula is renamed from 6 to 8 by explicit finite K derivations. The three
inner clauses have already had their conflicting coordinate binders renamed;
this module does not infer a restricted graph or quotient cancellation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedOuterAlpha
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactRestrictedForwardAlpha
open PASoundness.PAtoCompactRestrictedBackwardAlpha
open PASoundness.PAtoCompactRestrictedOrderAlpha
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

/-- The exact staged matrix, still with endpoint names 0,1 and graph name 6. -/
def alphaMatrix : Formula := conj (conj preparedForward alphaClause) alphaOrder

/-- Renaming the outer graph binder is justified by the concrete checks that
6 has no inner binder and 8 is absent from every name in the matrix. -/
def graph_alpha : ProofEquiv (.ex 6 alphaMatrix) (.ex 8 (replace 6 8 alphaMatrix)) :=
  ProofEquiv.alphaExists 6 8 alphaMatrix (by decide) (by decide) (by decide)

theorem graph_alpha_forward_certificate :
    theoremCode (certificate graph_alpha.forward) =
      imp (Formula.ex 6 alphaMatrix).encode (Formula.ex 8 (replace 6 8 alphaMatrix)).encode :=
  certificate_correct graph_alpha.forward

theorem graph_alpha_backward_certificate :
    theoremCode (certificate graph_alpha.backward) =
      imp (Formula.ex 8 (replace 6 8 alphaMatrix)).encode (Formula.ex 6 alphaMatrix).encode :=
  certificate_correct graph_alpha.backward

end PASoundness.PAtoCompactRestrictedOuterAlpha

#print axioms PASoundness.PAtoCompactRestrictedOuterAlpha.graph_alpha
#print axioms PASoundness.PAtoCompactRestrictedOuterAlpha.graph_alpha_forward_certificate
#print axioms PASoundness.PAtoCompactRestrictedOuterAlpha.graph_alpha_backward_certificate
