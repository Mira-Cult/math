import PASoundness.PAtoCompactMultiplicationForwardClauseClosed
import PASoundness.PAtoCompactMultiplicationReverseClauseClosed
import PASoundness.PAtoCompactMultiplicationFullPrefixNoGarbage
import PASoundness.PAtoCompactMultiplicationFullPrefixLex
import PASoundness.PAtoCompactProductNewMatrixShape

/-! Combine the actual forward, reverse, and lexicographic K derivations for
one extended product graph at free name 64. All underlying clean-graph,
candidate, cut, successor and row conditions remain in the shared context;
this module does not construct those witnesses or prove multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationSameWitnessMatrix
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationForwardSharedContext
open PASoundness.PAtoCompactMultiplicationForwardQuantGeneric
open PASoundness.PAtoCompactMultiplicationForwardClauseClosed
open PASoundness.PAtoCompactMultiplicationReverseClauseFromCases
open PASoundness.PAtoCompactMultiplicationReverseClauseClosed
open PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.PAtoCompactFixedFirstRowGraph64
open PASoundness.PAtoCompactMultiplicationFullPrefixNoGarbage
open PASoundness.PAtoCompactMultiplicationFullPrefixLex
open PASoundness.PAtoCompactProductNewLexShape
open PASoundness.PAtoCompactProductNewMatrixShape
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The explicit shared context proves the complete literal product matrix
at first factor 38, second factor 31, result 45, and the same graph 64. -/
def matrix_from_context : KDerivation (imp context.encode newMatrix.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [context.encode]
  have hc : Context Γ context.encode := .head _ _
  have hf : Context Γ matrixForward.encode := by
    change Context Γ newForward.encode
    exact .mp hc (.closed forward_clause)
  have hr : Context Γ matrixReverse.encode := by
    change Context Γ rebasedReverse.encode
    exact .mp hc (.closed reverse_clause)
  have hs : Context Γ sharedPremise.encode := .mp hc (.closed project_shared)
  have hrow : Context Γ rowBody64.encode := .mp hc (.closed project_row)
  have hng : Context Γ fullNoGarbage.encode := by
    change Context Γ (replace 0 31 (PAtoCompactFixedFirstCoverageBase.noGarbage 64)).encode
    exact .mp hrow (.closed full_prefix_no_garbage)
  have hl : Context Γ matrixLex.encode := by
    change Context Γ newLex.encode
    exact .mp hng (.mp hs (.closed full_prefix_lex))
  rw [matrix_clause_shape]
  simpa [namedBoth, Formula.encode, Formula.not, both, neg] using
    (Context.conjunctionIntro hf (Context.conjunctionIntro hr hl))

theorem matrix_from_context_certificate : theoremCode (certificate matrix_from_context) =
    imp context.encode newMatrix.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationSameWitnessMatrix
#print axioms PASoundness.PAtoCompactMultiplicationSameWitnessMatrix.matrix_from_context
#print axioms PASoundness.PAtoCompactMultiplicationSameWitnessMatrix.matrix_from_context_certificate
