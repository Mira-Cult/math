import PASoundness.PAtoCompactMultiplicationForwardSharedContext
import PASoundness.PAtoCompactMultiplicationOldForwardJointShapes
import PASoundness.PAtoCompactProductOldOutputPreimage
import PASoundness.PAtoCompactProductOldSuffixExclusion
import PASoundness.PAtoCompactMultiplicationFullPrefixOldEdge
import PASoundness.PAtoCompactMultiplicationSuffixPreimageFive
import PASoundness.PAtoCompactMultiplicationResultCutSplit

/-! Reverse-case projections from the same literal context used by the
forward and lexicographic multiplication proofs. The graph names are retained:
old graph 10, suffix map 6, and extended graph 64. No witness is constructed
and no product or soundness conclusion is asserted here. -/
namespace PASoundness.PAtoCompactMultiplicationReverseContextProjections
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactMultiplicationForwardSharedContext
open PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.PAtoCompactMultiplicationOldForwardJointShapes
open PASoundness.PAtoCompactFixedFirstRowGraph64 PASoundness.PAtoCompactFixedFirstPreservedBase
open PASoundness.PAtoCompactFixedFirstRowSuffixTarget40
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactZeroSuccessor
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Names for pointwise preimage and competitor queries may be generalized
because none is free in the common context. -/
def context_vacuity5 : KDerivation (imp context.encode (allCode 5 context.encode)) :=
  free_vacuity 5 context (by rw [context_free]; decide)
def context_vacuity7 : KDerivation (imp context.encode (allCode 7 context.encode)) :=
  free_vacuity 7 context (by rw [context_free]; decide)
def context_vacuity8 : KDerivation (imp context.encode (allCode 8 context.encode)) :=
  free_vacuity 8 context (by rw [context_free]; decide)

/-- The old reverse clause at the actual domain names. -/
def actualOldReverse : Formula := PAtoCompactProductOldOutputPreimage.oldReverse
private def actualOldForward : Formula :=
  replace 2 32 (replace 1 31 (replace 0 30 (replace 6 10 forwardFormula)))
private def actualOldLex : Formula :=
  replace 2 32 (replace 1 31 (replace 0 30 (replace 6 10 lexFormula)))
private theorem matrix_shape : oldMatrixActual = namedBoth actualOldForward
    (namedBoth actualOldReverse actualOldLex) := by decide

/-- Actual reverse clause follows from the literal old matrix in the common context. -/
def project_oldReverse : KDerivation (imp context.encode actualOldReverse.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [context.encode]
  have h : Context Γ sharedPremise.encode := .mp (.head _ _) (.closed project_shared)
  have h' : Context Γ (both oldMatrixActual.encode (both oldCleanActual.encode
      (both (PAtoCompactTermTranslation.domainAt 100 45).encode
        (both (PAtoCompactTermTranslation.domainAt 100 32).encode
          (both (PAtoCompactTermTranslation.domainAt 100 30).encode
            (both cutAlternative.encode (both suffixFilter.encode
              (both PAtoCompactMultiplicationNewRowSuffixOrder.suffixOrder.encode
                PAtoCompactMultiplicationSuffixCleanEdges.suffixClean.encode)))))))) := by
    simpa [sharedPremise,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hm : Context Γ oldMatrixActual.encode := Context.conjunctionLeft h'
  rw [matrix_shape] at hm
  have hm' : Context Γ (both actualOldForward.encode (both actualOldReverse.encode actualOldLex.encode)) := by
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using hm
  exact Context.conjunctionLeft (Context.conjunctionRight hm')

/-- Old-product cleanliness, at the exact names used by the reverse branch. -/
def project_oldClean : KDerivation (imp context.encode PAtoCompactProductOldSuffixExclusion.oldClean.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [context.encode]
  have h : Context Γ sharedPremise.encode := .mp (.head _ _) (.closed project_shared)
  have h' : Context Γ (both oldMatrixActual.encode (both oldCleanActual.encode
      (both (PAtoCompactTermTranslation.domainAt 100 45).encode
        (both (PAtoCompactTermTranslation.domainAt 100 32).encode
          (both (PAtoCompactTermTranslation.domainAt 100 30).encode
            (both cutAlternative.encode (both suffixFilter.encode
              (both PAtoCompactMultiplicationNewRowSuffixOrder.suffixOrder.encode
                PAtoCompactMultiplicationSuffixCleanEdges.suffixClean.encode)))))))) := by
    simpa [sharedPremise,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hc := Context.conjunctionLeft (Context.conjunctionRight h')
  have halign : oldCleanActual = PAtoCompactProductOldSuffixExclusion.oldClean := by decide
  simpa only [halign] using hc

/-- The clean suffix graph and filtered suffix are retained from the shared premise. -/
def project_suffixClean : KDerivation (imp context.encode
    PAtoCompactMultiplicationSuffixCleanEdges.suffixClean.encode) :=
  compose project_shared suffix_clean_projection

def project_filter : KDerivation (imp context.encode
    PAtoCompactMultiplicationResultCutSplit.suffixFilter) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [context.encode]
  have h : Context Γ sharedPremise.encode := .mp (.head _ _) (.closed project_shared)
  have h' : Context Γ (both oldMatrixActual.encode (both oldCleanActual.encode
      (both (PAtoCompactTermTranslation.domainAt 100 45).encode
        (both (PAtoCompactTermTranslation.domainAt 100 32).encode
          (both (PAtoCompactTermTranslation.domainAt 100 30).encode
            (both cutAlternative.encode (both suffixFilter.encode
              (both PAtoCompactMultiplicationNewRowSuffixOrder.suffixOrder.encode
                PAtoCompactMultiplicationSuffixCleanEdges.suffixClean.encode)))))))) := by
    simpa [sharedPremise,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hf := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight
    (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight
      (Context.conjunctionRight h'))))))
  simpa [suffixFilter,PAtoCompactMultiplicationResultCutSplit.suffixFilter,
    PAtoCompactFilterInstantiation.namedFilterBody,PAtoCompactFilteredSubset.filterGraph,
    PAtoCompactFilteredSubset.filterPredicate,namedBoth,Formula.not,Formula.encode,both,neg] using hf

/-- The original product graph remains a subgraph of the collected row graph. -/
def project_inclusion : KDerivation (imp context.encode (oldPreserved 64).encode) := by
  have h : KDerivation (imp rowBody64.encode
      (both (oldPreserved 64).encode
        (replace 0 31 (PAtoCompactFixedFirstCoverageBase.noGarbage 64)).encode)) := by
    simpa only [row_body64_shape] using row_projections
  apply Context.closeEmpty
  apply Context.deduction
  have hr : Context [context.encode] rowBody64.encode := .mp (.head _ _) (.closed project_row)
  exact Context.conjunctionLeft (.mp hr (.closed h))

/-- The new graph has the full-prefix no-garbage property. -/
def project_noGarbage : KDerivation (imp context.encode
    PAtoCompactMultiplicationFullPrefixOldEdge.fullNoGarbage.encode) := by
  have h : KDerivation (imp rowBody64.encode
      (both (oldPreserved 64).encode
        PAtoCompactMultiplicationFullPrefixOldEdge.fullNoGarbage.encode)) := by
    simpa only [row_body64_shape,PAtoCompactMultiplicationFullPrefixOldEdge.fullNoGarbage] using row_projections
  apply Context.closeEmpty
  apply Context.deduction
  have hr : Context [context.encode] rowBody64.encode := .mp (.head _ _) (.closed project_row)
  exact Context.conjunctionRight (.mp hr (.closed h))

/-- The suffix bijection uses the very same source, target, and graph names
as the reverse preimage theorem. -/
def project_suffixBijection : KDerivation (imp context.encode
    PAtoCompactMultiplicationSuffixPreimageFive.suffixBijection.encode) := by
  have he : mapBijection40 = PAtoCompactMultiplicationSuffixPreimageFive.suffixBijection := by decide
  simpa only [he] using project_map

end PASoundness.PAtoCompactMultiplicationReverseContextProjections
#print axioms PASoundness.PAtoCompactMultiplicationReverseContextProjections.context_vacuity5
#print axioms PASoundness.PAtoCompactMultiplicationReverseContextProjections.context_vacuity7
#print axioms PASoundness.PAtoCompactMultiplicationReverseContextProjections.context_vacuity8
#print axioms PASoundness.PAtoCompactMultiplicationReverseContextProjections.project_oldReverse
#print axioms PASoundness.PAtoCompactMultiplicationReverseContextProjections.project_oldClean
#print axioms PASoundness.PAtoCompactMultiplicationReverseContextProjections.project_suffixClean
#print axioms PASoundness.PAtoCompactMultiplicationReverseContextProjections.project_filter
#print axioms PASoundness.PAtoCompactMultiplicationReverseContextProjections.project_inclusion
#print axioms PASoundness.PAtoCompactMultiplicationReverseContextProjections.project_noGarbage
#print axioms PASoundness.PAtoCompactMultiplicationReverseContextProjections.project_suffixBijection
