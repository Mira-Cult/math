import PASoundness.PAtoCompactProductCleanFilter
import PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder
import PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
import PASoundness.PAtoCompactTermTranslation

/-! Concrete shared assumptions for four multiplication lexicographic cases.
The old matrix and graph hygiene are explicitly relocated to first factor 30,
second factor 31, old output 32, and graph 10. No hypotheses are constructed;
this does not establish row collection, product totality, or the PA bridge. -/
namespace PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductCleanFilter
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Literal old product matrix at graph 10 and operand/result names 30–32. -/
def oldMatrixActual : Formula := replace 2 32 (replace 1 31 (replace 0 30 (replace 6 10 productMatrix)))
/-- Explicit no-garbage condition on graph 10 at those same domains. -/
def oldCleanActual : Formula := replace 2 32 (replace 1 31 (replace 0 30
  (.all 19 (.imp (.member 10 19) (cleanPredicate 19)))))
def cutAlternative : Formula := namedEither (.equal 32 45) (.member 45 32)
def suffixFilter : Formula := .all 35 (namedFilterBody 45 40 35 (Formula.member 32 35).not)
/-- Common literal assumptions used by the four point cases. -/
def sharedPremise : Formula := namedBoth oldMatrixActual (namedBoth oldCleanActual
  (namedBoth (domainAt 100 45) (namedBoth (domainAt 100 32)
    (namedBoth (domainAt 100 30) (namedBoth cutAlternative
      (namedBoth suffixFilter (namedBoth suffixOrder suffixClean)))))))

/-- The concrete context projects the two supplied suffix graph conditions. -/
def suffix_projections : KDerivation (imp sharedPremise.encode
    (both suffixOrder.encode suffixClean.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hp : Context [sharedPremise.encode] sharedPremise.encode := .head [] _
  change Context [sharedPremise.encode] (both oldMatrixActual.encode
    (both oldCleanActual.encode (both (domainAt 100 45).encode (both (domainAt 100 32).encode
      (both (domainAt 100 30).encode (both cutAlternative.encode
        (both suffixFilter.encode (both suffixOrder.encode suffixClean.encode)))))))) at hp
  exact Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight
    (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight
      (Context.conjunctionRight hp))))))

def suffix_order_projection : KDerivation (imp sharedPremise.encode suffixOrder.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.conjunctionLeft (.mp (.head [] _) (.closed suffix_projections))

def suffix_clean_projection : KDerivation (imp sharedPremise.encode suffixClean.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.conjunctionRight (.mp (.head [] _) (.closed suffix_projections))

theorem suffix_projections_certificate : theoremCode (certificate suffix_projections) =
    imp sharedPremise.encode (both suffixOrder.encode suffixClean.encode) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationLexSharedContext
#print axioms PASoundness.PAtoCompactMultiplicationLexSharedContext.suffix_projections
#print axioms PASoundness.PAtoCompactMultiplicationLexSharedContext.suffix_order_projection
#print axioms PASoundness.PAtoCompactMultiplicationLexSharedContext.suffix_clean_projection
#print axioms PASoundness.PAtoCompactMultiplicationLexSharedContext.suffix_projections_certificate
