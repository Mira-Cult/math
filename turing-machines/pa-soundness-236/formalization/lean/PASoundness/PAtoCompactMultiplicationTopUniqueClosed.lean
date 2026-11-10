import PASoundness.PAtoCompactMultiplicationTopUniqueConditional
import PASoundness.PAtoCompactMultiplicationTopQueryClosed

/-! The top-row product-output uniqueness clause under the explicit old-graph
and suffix-graph hypotheses. K proves recovery of the suffix map edge, then
uses clean-map functionality. The graph witnesses themselves are supplied;
this is not product-graph existence or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationTopUniqueClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactProductOldSuffixExclusion
open PASoundness.PAtoCompactMultiplicationOldTripleIntro
open PASoundness.PAtoCompactMultiplicationTopQueryClosed
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactMultiplicationCleanMapUnique41
open PASoundness.PAtoCompactMultiplicationTopUniqueConditional
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The clean old graph, full-prefix row no-garbage, clean suffix map and its
bijection, and the selected source/map edge. -/
def assumptions : Formula := namedBoth oldClean
  (namedBoth (replace 0 31 (noGarbage 64))
    (namedBoth suffixClean (namedBoth mapBijection40
      (namedBoth (.member 31 3) (graphFormula 6 3 5)))))

private def parts (h : Context Γ assumptions.encode) :
    Context Γ (both oldClean.encode (both (replace 0 31 (noGarbage 64)).encode
      (both suffixClean.encode (both mapBijection40.encode
        (both (member 31 3) (graphFormula 6 3 5).encode))))) := by
  simpa [assumptions,namedBoth,Formula.not,Formula.encode,both,neg] using h

private def old_from_assumptions : KDerivation (imp assumptions.encode oldClean.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.conjunctionLeft (parts (.head _ _))
private def garbage_from_assumptions : KDerivation
    (imp assumptions.encode (replace 0 31 (noGarbage 64)).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.conjunctionLeft (Context.conjunctionRight (parts (.head _ _)))
private def clean_from_assumptions : KDerivation (imp assumptions.encode suffixClean.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (parts (.head _ _))))
private def map_from_assumptions : KDerivation (imp assumptions.encode mapBijection40.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight
    (Context.conjunctionRight (parts (.head _ _)))))
private def source_from_assumptions : KDerivation (imp assumptions.encode (member 31 3)) := by
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight
    (Context.conjunctionRight (Context.conjunctionRight (parts (.head _ _))))))
private def chosen_from_assumptions : KDerivation
    (imp assumptions.encode (graphFormula 6 3 5).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight
    (Context.conjunctionRight (Context.conjunctionRight (parts (.head _ _))))))

private def recover : KDerivation (imp assumptions.encode
    (imp (topTriple 70).encode (graphFormula 6 3 70).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(topTriple 70).encode,assumptions.encode]
  have ht : Context Γ (topTriple 70).encode := .head _ _
  have ha : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ oldClean.encode := .mp ha (.closed old_from_assumptions)
  have hn : Context Γ (replace 0 31 (noGarbage 64)).encode := .mp ha (.closed garbage_from_assumptions)
  have hr : Context Γ (both (member 31 3) (graphFormula 6 3 70).encode) := by
    simpa [topTriple] using (.mp ht (.mp hn (.mp hc (.closed top_query))))
  exact Context.conjunctionRight hr

/-- The selected top-row image is unique against every candidate output in
result 45, for the supplied clean old graph and full-prefix row invariant. -/
def top_unique : KDerivation (imp assumptions.encode topUnique.encode) :=
  unique_from_recovery assumptions (assumptions.vacuity 70 (by decide))
    clean_from_assumptions map_from_assumptions source_from_assumptions
    chosen_from_assumptions recover

theorem top_unique_certificate : theoremCode (certificate top_unique) =
    imp assumptions.encode topUnique.encode := certificate_correct top_unique
end PASoundness.PAtoCompactMultiplicationTopUniqueClosed
#print axioms PASoundness.PAtoCompactMultiplicationTopUniqueClosed.top_unique
#print axioms PASoundness.PAtoCompactMultiplicationTopUniqueClosed.top_unique_certificate
