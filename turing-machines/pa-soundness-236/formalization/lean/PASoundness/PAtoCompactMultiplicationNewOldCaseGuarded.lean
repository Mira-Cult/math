import PASoundness.PAtoCompactMultiplicationFourCaseLex
import PASoundness.PAtoCompactMultiplicationLexSharedContext
import PASoundness.PAtoCompactMultiplicationReverseMixedLex

/-! New-row/old-graph point case, conditional on an explicit finite K
old-graph endpoint extraction proof. The shared context and both graph
branches remain object-level antecedents. This does not infer cleanliness
from the old product matrix, construct the row, or prove multiplication. -/
namespace PASoundness.PAtoCompactMultiplicationNewOldCaseGuarded
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactMultiplicationRowQueryFirst PASoundness.PAtoCompactMultiplicationRowQueryFirstExists
open PASoundness.PAtoCompactMultiplicationFourCaseLex
open PASoundness.PAtoCompactMultiplicationMixedLexLogic PASoundness.PAtoCompactMultiplicationReverseMixedLex
open PASoundness.PAtoCompactMultiplicationSameRowLex
attribute [local irreducible] imp PASoundness.Cantor.pair PASoundness.Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The only extra proof-data input extracts the old major and output
memberships from the explicit clean-old hypothesis and actual old triple. -/
def new_old_from_endpoints
    (oldEndpoints : KDerivation (imp oldCleanActual.encode (imp oldSecond
      (both (member 30 7) (member 32 9))))) : KDerivation
    (imp sharedPremise.encode (imp newFirst (imp oldSecond comparisons))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldSecond,newFirst,sharedPremise.encode]
  have hold : Context Γ oldSecond := .head _ _
  have hnew : Context Γ newFirst := .hypothesis (by simp [Γ])
  have hp : Context Γ sharedPremise.encode := .hypothesis (by simp [Γ])
  have hp' := hp
  change Context Γ (both oldMatrixActual.encode
    (both oldCleanActual.encode (both (domainAt 100 45).encode (both (domainAt 100 32).encode
      (both (domainAt 100 30).encode (both cutAlternative.encode
        (both suffixFilter.encode (both suffixOrder.encode suffixClean.encode)))))))) at hp'
  have h0 := Context.conjunctionRight hp'
  have hclean : Context Γ oldCleanActual.encode := Context.conjunctionLeft h0
  have h1 := Context.conjunctionRight h0
  have h45 : Context Γ (domainAt 100 45).encode := Context.conjunctionLeft h1
  have h2 := Context.conjunctionRight h1
  have h32 : Context Γ (domainAt 100 32).encode := Context.conjunctionLeft h2
  have h3 := Context.conjunctionRight h2
  have h30 : Context Γ (domainAt 100 30).encode := Context.conjunctionLeft h3
  have h4 := Context.conjunctionRight h3
  have hcut : Context Γ (either (equal 32 45) (member 45 32)) := by
    simpa [cutAlternative,namedEither,Formula.not,Formula.encode,either,neg] using (Context.conjunctionLeft h4)
  have h5 := Context.conjunctionRight h4
  have hfilter : Context Γ (filterGraph 45 40 35 (neg (member 32 35))) := by
    simpa [suffixFilter,namedFilterBody,filterGraph,filterPredicate,namedBoth,Formula.not,Formula.encode,both,neg] using (Context.conjunctionLeft h5)
  have hsuffixClean : Context Γ suffixClean.encode := Context.conjunctionRight (Context.conjunctionRight h5)
  have hn : Context Γ (both (equal 3 30) (both (member 31 4) (graphFormula 6 4 5).encode)) := by
    have h := Context.mp hnew (.closed query_exists_elim)
    simpa [newFirst,queryResult,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have heq : Context Γ (equal 3 30) := Context.conjunctionLeft hn
  have hedge : Context Γ (graphFormula 6 4 5).encode := Context.conjunctionRight (Context.conjunctionRight hn)
  have hsuf : Context Γ (member 40 5) := Context.conjunctionRight
    (.mp hedge (.mp hsuffixClean (.closed (clean_endpoints 4 5 (by decide)))))
  have holdg : Context Γ (both (member 30 7) (member 32 9)) := .mp hold (.mp hclean (.closed oldEndpoints))
  have hout : Context Γ (both forwardComparison reverseComparison) :=
    .mp heq (.mp (Context.conjunctionLeft holdg) (.mp hsuf (.mp (Context.conjunctionRight holdg)
      (.mp hfilter (.mp hcut (.mp h30 (.mp h32 (.mp h45 (.closed candidate_reverse_mixed_lex)))))))))
  simpa [comparisons,forwardComparison,reverseComparison,oldToNewLex,newToOldLex,
    forwardClause,reverseClause,forwardLex,reverseLex] using hout

theorem new_old_from_endpoints_certificate
    (oldEndpoints : KDerivation (imp oldCleanActual.encode (imp oldSecond
      (both (member 30 7) (member 32 9))))) :
    theoremCode (certificate (new_old_from_endpoints oldEndpoints)) =
      imp sharedPremise.encode (imp newFirst (imp oldSecond comparisons)) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationNewOldCaseGuarded
#print axioms PASoundness.PAtoCompactMultiplicationNewOldCaseGuarded.new_old_from_endpoints
#print axioms PASoundness.PAtoCompactMultiplicationNewOldCaseGuarded.new_old_from_endpoints_certificate
