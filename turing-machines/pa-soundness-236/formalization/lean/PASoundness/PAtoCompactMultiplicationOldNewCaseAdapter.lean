import PASoundness.PAtoCompactMultiplicationFourCaseLex
import PASoundness.PAtoCompactMultiplicationLexSharedContext
import PASoundness.PAtoCompactMultiplicationActualMixedLex

/-! The old/new lexicographic point case under the explicit shared context.
The only supplied proof-data input extracts old graph endpoints from the
explicit clean-old hypothesis and actual old triple. This module does not
infer graph cleanliness from the product matrix, construct a row graph, prove
the entire product matrix, or establish multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationOldNewCaseAdapter
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationFourCaseLex
open PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.PAtoCompactMultiplicationRowQuerySecond PASoundness.PAtoCompactMultiplicationRowQuerySecondExists
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder PASoundness.PAtoCompactMultiplicationSameRowLex
open PASoundness.PAtoCompactMultiplicationMixedLexLogic PASoundness.PAtoCompactMultiplicationActualMixedLex
attribute [local irreducible] imp PASoundness.Cantor.pair PASoundness.Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Old/new case from an explicit finite-K old-endpoint extraction proof.
The supplied extractor requires the old graph's actual clean hypothesis. -/
def old_new_from_endpoint
    (oldEndpoints : KDerivation (imp oldCleanActual.encode (imp oldFirst
      (both (member 30 3) (both (member 31 4) (member 32 5)))))) :
    KDerivation (imp sharedPremise.encode (imp oldFirst (imp newSecond comparisons))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [newSecond,oldFirst,sharedPremise.encode]
  have hn : Context Γ newSecond := .head _ _
  have hold : Context Γ oldFirst := .hypothesis (by simp [Γ])
  have hp : Context Γ sharedPremise.encode := .hypothesis (by simp [Γ])
  change Context Γ (both oldMatrixActual.encode (both oldCleanActual.encode
    (both (domainAt 100 45).encode (both (domainAt 100 32).encode
      (both (domainAt 100 30).encode (both cutAlternative.encode
        (both suffixFilter.encode (both suffixOrder.encode suffixClean.encode)))))))) at hp
  have hclean : Context Γ oldCleanActual.encode := Context.conjunctionLeft (Context.conjunctionRight hp)
  have hrest := Context.conjunctionRight (Context.conjunctionRight hp)
  have hd45 : Context Γ (domainAt 100 45).encode := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hd32 : Context Γ (domainAt 100 32).encode := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hd30 : Context Γ (domainAt 100 30).encode := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hcut : Context Γ (either (equal 32 45) (member 45 32)) := by
    simpa [cutAlternative,namedEither,Formula.not,Formula.encode,either,neg] using Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hfilter : Context Γ (filterGraph 45 40 35 (neg (member 32 35))) := by
    simpa [suffixFilter,namedFilterBody,filterGraph,filterPredicate,namedBoth,Formula.not,Formula.encode,both,neg] using Context.conjunctionLeft hrest
  have hsuffix : Context Γ suffixClean.encode := Context.conjunctionRight (Context.conjunctionRight hrest)
  have heold : Context Γ (both (member 30 3) (both (member 31 4) (member 32 5))) :=
    .mp hold (.mp hclean (.closed oldEndpoints))
  have hnew : Context Γ (both (equal 7 30) (both (member 31 8) (graphFormula 6 8 9).encode)) := by
    have h := Context.mp hn (.closed query_second_exists_elim)
    simpa [newSecond,queryResultSecond,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hedge : Context Γ (graphFormula 6 8 9).encode := Context.conjunctionRight (Context.conjunctionRight hnew)
  have hend : Context Γ (both (member 31 8) (member 40 9)) :=
    .mp hedge (.mp hsuffix (.closed (clean_endpoints 8 9 (by decide))))
  have hresult := Context.mp (Context.conjunctionLeft hnew)
    (Context.mp (Context.conjunctionLeft heold)
      (Context.mp (Context.conjunctionRight hend)
        (Context.mp (Context.conjunctionRight (Context.conjunctionRight heold))
          (Context.mp hfilter (Context.mp hcut (Context.mp hd30 (Context.mp hd32
            (Context.mp hd45 (.closed candidate_mixed_lex_30)))))))))
  simpa [comparisons,forwardClause,reverseClause,forwardComparison,reverseComparison,
    forwardLex,reverseLex,oldToNewLex,newToOldLex] using hresult

theorem old_new_from_endpoint_certificate
    (oldEndpoints : KDerivation (imp oldCleanActual.encode (imp oldFirst
      (both (member 30 3) (both (member 31 4) (member 32 5)))))) :
    theoremCode (certificate (old_new_from_endpoint oldEndpoints)) =
      imp sharedPremise.encode (imp oldFirst (imp newSecond comparisons)) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationOldNewCaseAdapter
#print axioms PASoundness.PAtoCompactMultiplicationOldNewCaseAdapter.old_new_from_endpoint
#print axioms PASoundness.PAtoCompactMultiplicationOldNewCaseAdapter.old_new_from_endpoint_certificate
