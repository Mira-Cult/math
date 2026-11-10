import PASoundness.PAtoCompactMultiplicationFullPrefixSuffixEdge
import PASoundness.PAtoCompactMultiplicationRowCompetitorUnique
import PASoundness.PAtoCompactMultiplicationCompetitorTripleLift

/-! A finite K suffix-output competitor uniqueness theorem for the fixed-first
product row. The old graph is clean, the row graph has its full-prefix
no-garbage condition, and one selected suffix-map edge is explicit. The same
nested edge witnesses are retained through branch classification. This is not
a complete reverse product clause, multiplication totality, or PA soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationSuffixCompetitorClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactProductOldSuffixExclusion
open PASoundness.PAtoCompactMultiplicationFullPrefixOldEdge
open PASoundness.PAtoCompactMultiplicationFullPrefixSuffixEdge
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactMultiplicationSuffixInjective41
open PASoundness.PAtoCompactMultiplicationRowCompetitorUnique
open PASoundness.PAtoCompactMultiplicationCompetitorTripleLift
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def filterF : Formula := .all 35
  (namedFilterBody 45 40 35 (Formula.member 32 35).not)
/-- All required assumptions refer to one old graph, one row graph and one
suffix map; output 5 lies in suffix 40 and map edge (41,5) is supplied. -/
def assumptions : Formula := namedBoth fullNoGarbage (namedBoth oldClean
  (namedBoth filterF (namedBoth (.member 40 5)
    (namedBoth suffixClean (namedBoth suffixBijection (graphFormula 6 41 5))))))

private def point : KDerivation (imp assumptions.encode (imp competitorPairs.encode
    (imp (member 64 63) competitorEqualities.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 64 63,competitorPairs.encode,assumptions.encode]
  have hm : Context Γ (member 64 63) := .head _ _
  have hq : Context Γ competitorPairs.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ (both fullNoGarbage.encode (both oldClean.encode
      (both (filterGraph 45 40 35 (neg (member 32 35))) (both (member 40 5)
        (both suffixClean.encode (both suffixBijection.encode (graphFormula 6 41 5).encode)))))) := by
    have h : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
    simpa [assumptions,filterF,namedFilterBody,namedBoth,Formula.not,Formula.encode,
      filterGraph,filterPredicate,both,neg] using h
  have hg := Context.conjunctionLeft ha
  have hr1 := Context.conjunctionRight ha
  have hc := Context.conjunctionLeft hr1
  have hr2 := Context.conjunctionRight hr1
  have hf := Context.conjunctionLeft hr2
  have hr3 := Context.conjunctionRight hr2
  have hs := Context.conjunctionLeft hr3
  have hr4 := Context.conjunctionRight hr3
  have hfc := Context.conjunctionLeft hr4
  have hr5 := Context.conjunctionRight hr4
  have hfb := Context.conjunctionLeft hr5
  have hedge := Context.conjunctionRight hr5
  have hq' : Context Γ PASoundness.PAtoCompactMultiplicationRowQueryCompetitor.competitorPairs.encode := by
    simpa [PASoundness.PAtoCompactMultiplicationRowQueryCompetitor.competitorPairs,
      PASoundness.PAtoCompactMultiplicationCompetitorTripleLift.competitorPairs] using hq
  have hrow : Context Γ fullRowWitness.encode :=
    .mp hm (.mp hq' (.mp hs (.mp hf (.mp hc (.mp hg (.closed suffix_output_edge_is_row))))))
  have hresult : Context Γ (both (equal 7 30) (equal 8 41)) :=
    .mp hrow (.mp hq' (.mp hedge (.mp hfb (.mp hfc (.closed row_competitor_unique)))))
  simpa [competitorEqualities,namedBoth,Formula.not,Formula.encode,both,neg] using hresult

/-- Every competing triple ending at the selected suffix output has major
coordinate 30 and minor coordinate 41. The theorem derives actual finite K
proof data from the displayed graph/filter assumptions, with no supplied
pointwise proof. -/
def suffix_competitor_unique : KDerivation (imp assumptions.encode
    (imp competitorTriple.encode competitorEqualities.encode)) :=
  competitor_of_point assumptions (by decide) (by decide) point

theorem suffix_competitor_unique_certificate : theoremCode (certificate suffix_competitor_unique) =
    imp assumptions.encode (imp competitorTriple.encode competitorEqualities.encode) :=
  certificate_correct suffix_competitor_unique
end PASoundness.PAtoCompactMultiplicationSuffixCompetitorClosed
#print axioms PASoundness.PAtoCompactMultiplicationSuffixCompetitorClosed.suffix_competitor_unique
#print axioms PASoundness.PAtoCompactMultiplicationSuffixCompetitorClosed.suffix_competitor_unique_certificate
