import PASoundness.PAtoCompactProductOutputAssembledGraph
import PASoundness.PAtoCompactProductOutputReverseAlignment
import PASoundness.PAtoCompactProductOutputOrderAlignment

/-! Assemble the literal canonical target product matrix from the same
collected graph's forward, reverse and order clauses. The source candidate,
source product matrix and output-isomorphism bijection/order are explicit.
This is not yet arbitrary-name term-graph output transport. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputCanonical

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactProductOutputAssembledGraph
open PASoundness.PAtoCompactProductOutputForwardAlignment PASoundness.PAtoCompactProductOutputReverseAlignment
open PASoundness.PAtoCompactProductOutputOrderAlignment

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def baseMatrix : Formula := replace 2 42 (replace 1 44 (replace 0 43
  PAtoCompactMultiplicationCandidate.productMatrix))
def targetMatrix : Formula := replace 6 58 baseMatrix
def targetProduct : Formula := .ex 6 baseMatrix

theorem target_matrix_shape : targetMatrix = namedBoth canonicalForward
    (namedBoth canonicalReverse canonicalOrder) := by decide

/-- The three clauses retained at graph58 imply the literal target matrix. -/
def assembled_to_matrix : KDerivation (imp assembledGraph.encode targetMatrix.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [assembledGraph.encode]
  have hg : Context Γ assembledGraph.encode := .head _ _
  have hg' : Context Γ (both PAtoCompactProductOutputActualPoint.actualInvariant.encode
      (both PAtoCompactProductOutputForwardClauseAll.forwardClause.encode
        (both PAtoCompactProductOutputReverseClauseAll.reverseClause.encode
          PAtoCompactProductOutputLexGraphAll.graphOrder.encode))) := by
    simpa [assembledGraph, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have hf := Context.mp (Context.conjunctionLeft (Context.conjunctionRight hg')) (.closed forward_alignment)
  have hr := Context.mp (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg'))) (.closed reverse_alignment)
  have ho := Context.mp (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg'))) (.closed order_alignment)
  simpa [target_matrix_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
    Context.conjunctionIntro hf (Context.conjunctionIntro hr ho)

/-- Under the source candidate, source product matrix and an ordered output
bijection, construct the canonical target product relation for factors43/44
and output42. This is noncomputable finite K proof data, not an executable
certificate extractor. -/
noncomputable def canonical_product_output : KDerivation (imp extendedAssumptions.encode
    (imp (candidateCode 0 81 77 78 72 64 73 59 75) targetProduct.encode)) := by
  have hmap := existsCongr 58 assembled_to_matrix
  have halpha := (existentialAlpha 6 58 baseMatrix (by decide) (by decide) (by decide)).2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [candidateCode 0 81 77 78 72 64 73 59 75,extendedAssumptions.encode]
  have hc : Context Γ (candidateCode 0 81 77 78 72 64 73 59 75) := .head _ _
  have ha : Context Γ extendedAssumptions.encode := .hypothesis (by simp [Γ])
  have hg := Context.mp hc (Context.mp ha (.closed assembled_graph))
  have hm := Context.mp hg (.closed hmap)
  have ht := Context.mp hm (.closed halpha)
  simpa [targetMatrix, targetProduct, CompactNamed.Formula.encode] using ht

theorem canonical_product_output_certificate : theoremCode (certificate canonical_product_output) =
    imp extendedAssumptions.encode (imp (candidateCode 0 81 77 78 72 64 73 59 75)
      targetProduct.encode) := certificate_correct _

end PASoundness.PAtoCompactProductOutputCanonical

#print axioms PASoundness.PAtoCompactProductOutputCanonical.assembled_to_matrix
#print axioms PASoundness.PAtoCompactProductOutputCanonical.canonical_product_output
#print axioms PASoundness.PAtoCompactProductOutputCanonical.canonical_product_output_certificate
