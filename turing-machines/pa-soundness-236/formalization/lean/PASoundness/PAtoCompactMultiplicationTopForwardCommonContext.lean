import PASoundness.PAtoCompactMultiplicationForwardSharedContext
import PASoundness.PAtoCompactMultiplicationTopPointTransport

/-! Projection of the shared product-successor context into the antecedents
of the top-forward point. The same old graph, suffix map and collected row
are retained. No graph witnesses or multiplication theorem are constructed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationTopForwardCommonContext
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFixedFirstCoverageBase PASoundness.PAtoCompactFixedFirstPreservedBase
open PASoundness.PAtoCompactFixedFirstRowGraph64
open PASoundness.PAtoCompactMultiplicationForwardSharedContext
open PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.PAtoCompactMultiplicationTopPointTransport
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactMultiplicationTopCoverageWitness
open PASoundness.PAtoCompactTermTranslation
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private theorem clean_shape : oldCleanActual = PASoundness.PAtoCompactProductOldSuffixExclusion.oldClean := by decide
private theorem map_shape : PASoundness.PAtoCompactFixedFirstRowSuffixTarget40.mapBijection40 =
    PASoundness.PAtoCompactMultiplicationCleanMapUnique41.mapBijection40 := by rfl
private theorem filter_shape : PASoundness.PAtoCompactMultiplicationLexSharedContext.suffixFilter =
    PASoundness.PAtoCompactMultiplicationTopCoverageWitness.suffixFilter := by rfl
private theorem row_shape : rowBody64 = namedBoth (oldPreserved 64)
    (namedBoth (replace 0 31 (coverage 64)) (replace 0 31 (noGarbage 64))) := by decide

/-- The literal shared context entails the point-independent conditions of
the top-forward point. The graph names and witness values are unchanged. -/
def shared_to_top_base : KDerivation (imp context.encode base.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [context.encode]
  have hp : Context Γ context.encode := .head _ _
  have hs : Context Γ sharedPremise.encode := .mp hp (.closed project_shared)
  have hm : Context Γ PASoundness.PAtoCompactFixedFirstRowSuffixTarget40.mapBijection40.encode :=
    .mp hp (.closed project_map)
  have hr : Context Γ rowBody64.encode := .mp hp (.closed project_row)
  have hs' : Context Γ (both oldMatrixActual.encode (both oldCleanActual.encode
      (both (domainAt 100 45).encode (both (domainAt 100 32).encode
        (both (domainAt 100 30).encode (both cutAlternative.encode
          (both PASoundness.PAtoCompactMultiplicationLexSharedContext.suffixFilter.encode
            (both PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder.suffixOrder.encode suffixClean.encode)))))))) := by
    simpa [sharedPremise,namedBoth,Formula.not,Formula.encode,both,neg] using hs
  have hc : Context Γ PASoundness.PAtoCompactProductOldSuffixExclusion.oldClean.encode := by
    simpa only [clean_shape] using (Context.conjunctionLeft (Context.conjunctionRight hs'))
  have htail := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight
    (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hs')))))
  have hf : Context Γ PASoundness.PAtoCompactMultiplicationTopCoverageWitness.suffixFilter.encode := by
    simpa only [filter_shape] using (Context.conjunctionLeft htail)
  have hclean : Context Γ suffixClean.encode :=
    Context.conjunctionRight (Context.conjunctionRight htail)
  have hctx : Context Γ witnessContext.encode := by
    have h := Context.conjunctionIntro hclean hf
    simpa [witnessContext,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hrow : Context Γ (both (oldPreserved 64).encode
      (both (replace 0 31 (coverage 64)).encode (replace 0 31 (noGarbage 64)).encode)) := by
    rw [row_shape] at hr
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using hr
  have hmap : Context Γ PASoundness.PAtoCompactMultiplicationCleanMapUnique41.mapBijection40.encode := by
    simpa only [map_shape] using hm
  have h := Context.conjunctionIntro hc
    (Context.conjunctionIntro (Context.conjunctionRight (Context.conjunctionRight hrow))
      (Context.conjunctionIntro hctx (Context.conjunctionIntro hmap
        (Context.conjunctionLeft (Context.conjunctionRight hrow)))))
  simpa [base,namedBoth,Formula.not,Formula.encode,both,neg] using h

theorem shared_to_top_base_certificate : theoremCode (certificate shared_to_top_base) =
    imp context.encode base.encode := certificate_correct shared_to_top_base
end PASoundness.PAtoCompactMultiplicationTopForwardCommonContext
#print axioms PASoundness.PAtoCompactMultiplicationTopForwardCommonContext.shared_to_top_base
#print axioms PASoundness.PAtoCompactMultiplicationTopForwardCommonContext.shared_to_top_base_certificate
