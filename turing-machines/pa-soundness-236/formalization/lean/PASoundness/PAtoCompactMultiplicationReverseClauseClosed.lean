import PASoundness.PAtoCompactMultiplicationReverseWitnessShape
import PASoundness.PAtoCompactMultiplicationOldReverseCommonContext
import PASoundness.PAtoCompactMultiplicationSuffixReverseCaseFixed

/-! The full reverse clause of the product-successor matrix, conditional on the
explicit common object-level graph context. Both old and suffix output cases
are actual finite K derivations. This does not construct the context, prove
the full product matrix, establish multiplication totality or PA soundness. -/
namespace PASoundness.PAtoCompactMultiplicationReverseClauseClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactMultiplicationForwardSharedContext
open PASoundness.PAtoCompactMultiplicationReverseContextProjections
open PASoundness.PAtoCompactMultiplicationReverseClauseFromCases
open PASoundness.PAtoCompactMultiplicationReverseWitnessShape
open PASoundness.PAtoCompactMultiplicationOldReverseCommonContext
open PASoundness.PAtoCompactProductOldOutputWitnessFromReflection
open PASoundness.PAtoCompactMultiplicationReverseWitnessFromPoint
open PASoundness.PAtoCompactMultiplicationSuffixReverseCaseFixed
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The old-output team's witness is exactly the body extracted from the
literal renamed reverse clause. -/
theorem old_witness_alignment : reverseWitness5 =
    PAtoCompactProductOldOutputWitnessFromReflection.targetWitness := by
  apply witness_of_shape
  simpa [rebasedReverse] using target_witness_shape

/-- The suffix team's witness is the same literal reverse-clause body. -/
theorem suffix_witness_alignment : reverseWitness5 =
    .ex 3 (.ex 4 PAtoCompactMultiplicationReverseWitnessFromPoint.targetBody) := by
  apply witness_of_shape
  simpa [rebasedReverse] using reverse_clause_syntax

/-- The entire literal reverse clause for graph64 and factors38/31/result45
follows from the shared, explicit successor/graph/cleanliness/candidate context.
The old and suffix preimages are both constructed inside the imported K proofs. -/
def reverse_clause : KDerivation (imp context.encode rebasedReverse.encode) := by
  have hold : KDerivation (imp context.encode (imp (member 32 5) reverseWitness5.encode)) := by
    rw [old_witness_alignment]
    exact old_reverse_case
  have hsuffix : KDerivation (imp context.encode (imp (member 40 5) reverseWitness5.encode)) := by
    rw [suffix_witness_alignment]
    simpa [Formula.encode] using suffix_case
  exact reverse_clause_from_cases context context_vacuity5 project_filter hold hsuffix

theorem reverse_clause_certificate : theoremCode (certificate reverse_clause) =
    imp context.encode rebasedReverse.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationReverseClauseClosed
#print axioms PASoundness.PAtoCompactMultiplicationReverseClauseClosed.old_witness_alignment
#print axioms PASoundness.PAtoCompactMultiplicationReverseClauseClosed.suffix_witness_alignment
#print axioms PASoundness.PAtoCompactMultiplicationReverseClauseClosed.reverse_clause
#print axioms PASoundness.PAtoCompactMultiplicationReverseClauseClosed.reverse_clause_certificate
