import PASoundness.PAtoCompactSeededSpanGlobalOrderLift
import PASoundness.PAtoCompactOrderIsoInstance

/-! Alpha-convert the proved 2/26/3/27 quantified point clause to the literal
graph-9 order clause on whole source 0 and whole target 8. The same explicit
global guard remains; this does not establish bijection or sum functionality. -/
namespace PASoundness.PAtoCompactSeededSpanCanonicalOrder

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoInstance
open PASoundness.PAtoCompactSeededSpanGlobalOrderPoint PASoundness.PAtoCompactSeededSpanGlobalOrderLift

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def targetOrder : Formula := replace 6 9 (replace 1 8 orderFormula)
private def targetMatrix : Formula := replace 6 9 (replace 1 8 orderMatrix)
private def moved4 : Formula := replace 4 26 targetMatrix
private def moved5 : Formula := replace 5 27 moved4
private def body4 : Formula := .all 3 (.all 5 targetMatrix)

private theorem point_alignment : moved5 = pointClause := by decide
private theorem target_alignment : targetOrder = .all 2 (.all 4 (.all 3 (.all 5 targetMatrix))) := by decide
private theorem body_alignment : replace 4 26 body4 = .all 3 (.all 5 moved4) := by decide

/-- Convert the fresh-point quantified order to the canonical order binders
using only K universal-alpha congruence. -/
def quantified_order_to_canonical : KDerivation (imp quantifiedOrder.encode targetOrder.encode) := by
  have h5 := (universalAlpha 5 27 moved4 (by decide) (by decide) (by decide)).2
  have h4 := (universalAlpha 4 26 body4 (by decide) (by decide) (by decide)).2
  rw [body_alignment] at h4
  have h26 : KDerivation (imp (allCode 26 (allCode 3 (allCode 27 moved5.encode)))
      (allCode 26 (allCode 3 (allCode 5 moved4.encode)))) := by
    simpa only [moved5] using allCongr 26 (allCongr 3 h5)
  have h4' : KDerivation (imp (allCode 26 (allCode 3 (allCode 5 moved4.encode)))
      (allCode 4 (allCode 3 (allCode 5 targetMatrix.encode)))) := by
    simpa only [body4,Formula.encode] using h4
  have h2 := allCongr 2 (compose h26 h4')
  rw [point_alignment] at h2
  simpa only [quantifiedOrder,target_alignment,Formula.encode] using h2

/-- The exact graph-9 order formula follows under the same explicit global
guard that supplies the seed, candidate, cut, filter and input-order data. -/
def seeded_span_canonical_order : KDerivation (imp globalGuard.encode targetOrder.encode) :=
  compose global_order_lift quantified_order_to_canonical

theorem seeded_span_canonical_order_certificate : theoremCode (certificate seeded_span_canonical_order) =
    imp globalGuard.encode targetOrder.encode := certificate_correct seeded_span_canonical_order

end PASoundness.PAtoCompactSeededSpanCanonicalOrder

#print axioms PASoundness.PAtoCompactSeededSpanCanonicalOrder.targetOrder
#print axioms PASoundness.PAtoCompactSeededSpanCanonicalOrder.quantified_order_to_canonical
#print axioms PASoundness.PAtoCompactSeededSpanCanonicalOrder.seeded_span_canonical_order
#print axioms PASoundness.PAtoCompactSeededSpanCanonicalOrder.seeded_span_canonical_order_certificate
