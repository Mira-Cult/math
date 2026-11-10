import PASoundness.PAtoCompactSeededSpanConditionalBijection
import PASoundness.PAtoCompactSeededSpanCanonicalOrder
import PASoundness.PAtoCompactConditionalTransitivityMatrix

/-! Assemble the same graph9's conditional literal bijection and order
matrix. The guard retains the full graph/seed/clean/filter/candidate/cut
assumptions of both components, including the two whole-domain order clauses.
This does not construct a graph or establish general addition congruence. -/
namespace PASoundness.PAtoCompactSeededSpanConditionalMatrix

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactScopedActiveReplace

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def fullOrderGuard : Formula := replace 10 1 PASoundness.PAtoCompactSeededSpanGlobalOrderPoint.globalGuard
def guard : Formula := namedBoth PASoundness.PAtoCompactSeededSpanConditionalBijection.guard fullOrderGuard
def targetMatrix : Formula := namedBoth PASoundness.PAtoCompactSeededSpanConditionalBijection.targetBijection
  PASoundness.PAtoCompactSeededSpanCanonicalOrder.targetOrder

/-- The assembled target is the literal isomorphism matrix on graph9,
source0 and target8, not a semantic equivalence assertion. -/
theorem target_matrix_exact : targetMatrix = replace 6 9 (replace 1 8
    PASoundness.PAtoCompactConditionalTransitivityMatrix.sourceMatrix) := by decide

private def orderFrame : Formula := .imp PASoundness.PAtoCompactSeededSpanGlobalOrderPoint.globalGuard
  PASoundness.PAtoCompactSeededSpanCanonicalOrder.targetOrder
private theorem order_frame_alignment : replace 10 1 orderFrame = .imp fullOrderGuard
    PASoundness.PAtoCompactSeededSpanCanonicalOrder.targetOrder := by decide

private def full_order : KDerivation (imp fullOrderGuard.encode
    PASoundness.PAtoCompactSeededSpanCanonicalOrder.targetOrder.encode) := by
  have hbase : KDerivation orderFrame.encode := by
    simpa only [orderFrame,Formula.encode] using PASoundness.PAtoCompactSeededSpanCanonicalOrder.seeded_span_canonical_order
  have h := replace_derivation 10 1 orderFrame (by decide) (by decide) hbase
  rw [order_frame_alignment] at h
  exact h

/-- The same supplied graph9 satisfies both the literal bijection and order
clauses under the unchanged conditional component guards. -/
def conditional_isomorphism_matrix : KDerivation (imp guard.encode targetMatrix.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hb : Context Γ PASoundness.PAtoCompactSeededSpanConditionalBijection.guard.encode := Context.conjunctionLeft hg
  have ho : Context Γ fullOrderGuard.encode := Context.conjunctionRight hg
  have hbij : Context Γ PASoundness.PAtoCompactSeededSpanConditionalBijection.targetBijection.encode :=
    .mp hb (.closed PASoundness.PAtoCompactSeededSpanConditionalBijection.conditional_bijection)
  have horder : Context Γ PASoundness.PAtoCompactSeededSpanCanonicalOrder.targetOrder.encode :=
    .mp ho (.closed full_order)
  exact Context.conjunctionIntro hbij horder

theorem conditional_isomorphism_matrix_certificate : theoremCode (certificate conditional_isomorphism_matrix) =
    imp guard.encode targetMatrix.encode := certificate_correct conditional_isomorphism_matrix

end PASoundness.PAtoCompactSeededSpanConditionalMatrix

#print axioms PASoundness.PAtoCompactSeededSpanConditionalMatrix.fullOrderGuard
#print axioms PASoundness.PAtoCompactSeededSpanConditionalMatrix.guard
#print axioms PASoundness.PAtoCompactSeededSpanConditionalMatrix.targetMatrix
#print axioms PASoundness.PAtoCompactSeededSpanConditionalMatrix.target_matrix_exact
#print axioms PASoundness.PAtoCompactSeededSpanConditionalMatrix.conditional_isomorphism_matrix
#print axioms PASoundness.PAtoCompactSeededSpanConditionalMatrix.conditional_isomorphism_matrix_certificate
