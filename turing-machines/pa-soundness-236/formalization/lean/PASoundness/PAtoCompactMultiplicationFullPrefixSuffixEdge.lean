import PASoundness.PAtoCompactMultiplicationFullPrefixOldEdge
import PASoundness.PAtoCompactProductOldCompetitorSuffixExclusion

/-! Under the actual full-prefix no-garbage invariant, a queried edge whose
output belongs to the literal suffix cannot be an old graph edge. This keeps
the same represented outer edge and does not assume pair extensionality,
product matrix completeness or multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationFullPrefixSuffixEdge
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactProductOldSuffixExclusion
open PASoundness.PAtoCompactProductOldCompetitorSuffixExclusion
open PASoundness.PAtoCompactMultiplicationRowQueryCompetitor
open PASoundness.PAtoCompactMultiplicationFullPrefixOldEdge
open PASoundness.PAtoCompactMultiplicationResultCutSplit
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private theorem query_alignment : competitorQuery = competitorPairs := by decide

private def no_garbage_at_63 : KDerivation (imp fullNoGarbage.encode
    (imp (member 64 63) (either (member 10 63) fullRowWitness.encode))) := by
  let F : Formula := .imp (.member 64 9)
    (namedEither (.member 10 9) (replace 0 31 rowWitness))
  have hsource : fullNoGarbage = .all 9 F := by decide
  have hi := universalInstance 9 63 F (by decide) (by decide) (by decide)
  have hshape : replace 9 63 F = .imp (.member 64 63)
      (namedEither (.member 10 63) fullRowWitness) := by decide
  rw [hshape] at hi
  rw [hsource]
  simpa [F,namedEither,Formula.not,Formula.encode,neg,either] using hi

/-- With the full-prefix no-garbage condition and a clean old graph, a queried
edge in graph64 whose output5 lies in suffix40 has the full-prefix row
witness at that same outer edge63. -/
def suffix_output_edge_is_row : KDerivation
    (imp fullNoGarbage.encode (imp oldClean.encode
      (imp (filterGraph 45 40 35 (neg (member 32 35))) (imp (member 40 5)
        (imp competitorPairs.encode (imp (member 64 63) fullRowWitness.encode)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 64 63,competitorPairs.encode,member 40 5,
    filterGraph 45 40 35 (neg (member 32 35)),oldClean.encode,fullNoGarbage.encode]
  have hm : Context Γ (member 64 63) := .head _ _
  have hq : Context Γ competitorPairs.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (member 40 5) := .hypothesis (by simp [Γ])
  have hf : Context Γ (filterGraph 45 40 35 (neg (member 32 35))) := .hypothesis (by simp [Γ])
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ fullNoGarbage.encode := .hypothesis (by simp [Γ])
  have hq' : Context Γ competitorQuery.encode := by simpa only [query_alignment] using hq
  have hn : Context Γ (neg (member 10 63)) :=
    .mp hs (.mp hf (.mp hq' (.mp hc (.closed old_competitor_excluded))))
  have hcases : Context Γ (either (member 10 63) fullRowWitness.encode) :=
    .mp hm (.mp hg (.closed no_garbage_at_63))
  apply Context.disjunctionElim hcases
  · let Δ := member 10 63 :: Γ
    have he : Context Δ (member 10 63) := .head _ _
    exact Context.explode fullRowWitness.encode (.mp he (.under hn _))
  · exact Context.head _ _

theorem suffix_output_edge_is_row_certificate :
    theoremCode (certificate suffix_output_edge_is_row) =
      imp fullNoGarbage.encode (imp oldClean.encode
        (imp (filterGraph 45 40 35 (neg (member 32 35))) (imp (member 40 5)
          (imp competitorPairs.encode (imp (member 64 63) fullRowWitness.encode))))) :=
  certificate_correct suffix_output_edge_is_row
end PASoundness.PAtoCompactMultiplicationFullPrefixSuffixEdge
#print axioms PASoundness.PAtoCompactMultiplicationFullPrefixSuffixEdge.suffix_output_edge_is_row
#print axioms PASoundness.PAtoCompactMultiplicationFullPrefixSuffixEdge.suffix_output_edge_is_row_certificate
