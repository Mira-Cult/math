import PASoundness.PAtoCompactMultiplicationRowQueryCompetitorFull
import PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
import PASoundness.PAtoCompactMultiplicationResultCutSplit

/-! For an old-result output, the full-prefix new-row classification is
impossible. This pointwise K argument classifies the very same edge as old;
it does not prove a product bijection or multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationFullPrefixOldEdge
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationRowQueryCompetitor
open PASoundness.PAtoCompactMultiplicationRowQueryCompetitorFull
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactMultiplicationResultCutSplit
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The actual full-prefix no-garbage condition at graph 64. -/
def fullNoGarbage : Formula := replace 0 31 (noGarbage 64)
/-- The actual new-row branch at outer edge name 63 and full source prefix. -/
def fullRowWitness : Formula := replace 9 63 (replace 0 31 rowWitness)

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

/-- Under explicit no-garbage, map-cleanliness and filtered-suffix premises,
a queried new-graph edge producing an old-result member is the same old
edge 63. Competitor coordinates are 7 and 8 and the common output is 5. -/
def old_output_edge_is_old : KDerivation
    (imp fullNoGarbage.encode (imp suffixClean.encode
      (imp (filterGraph 45 40 35 (neg (member 32 35))) (imp (member 32 5)
        (imp competitorPairs.encode (imp (member 64 63) (member 10 63))))))) := by
  apply Context.closeEmpty
  repeat apply Context.deduction
  let Γ := [member 64 63,competitorPairs.encode,member 32 5,
    filterGraph 45 40 35 (neg (member 32 35)),suffixClean.encode,fullNoGarbage.encode]
  have hm : Context Γ (member 64 63) := .head _ _
  have hq : Context Γ competitorPairs.encode := .hypothesis (by simp [Γ])
  have ho : Context Γ (member 32 5) := .hypothesis (by simp [Γ])
  have hf : Context Γ (filterGraph 45 40 35 (neg (member 32 35))) := .hypothesis (by simp [Γ])
  have hc : Context Γ suffixClean.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ fullNoGarbage.encode := .hypothesis (by simp [Γ])
  have hcases : Context Γ (either (member 10 63) fullRowWitness.encode) :=
    .mp hm (.mp hg (.closed no_garbage_at_63))
  apply Context.disjunctionElim hcases
  · exact Context.head _ _
  · let Δ := fullRowWitness.encode :: Γ
    have hr : Context Δ fullRowWitness.encode := .head _ _
    have hqresult : Context Δ competitorResult.encode :=
      .mp hr (.mp (.under hq _) (.closed row_query_full_prefix))
    have hparts : Context Δ (both (equal 7 30) (both (member 31 8) (graphFormula 6 8 5).encode)) := by
      simpa [competitorResult,namedBoth,Formula.not,Formula.encode,both,neg] using hqresult
    have hedge := Context.conjunctionRight (Context.conjunctionRight hparts)
    have hend := Context.mp hedge (.mp (.under hc _) (.closed (clean_endpoints 8 5 (by decide))))
    have hsuffix := Context.conjunctionRight hend
    have hn : Context Δ (neg (member 32 5)) :=
      .mp hsuffix (.mp (.under hf _) (.closed (old_suffix_disjoint 5 (by decide))))
    exact Context.explode (member 10 63) (.mp (.under ho _) hn)

theorem old_output_edge_is_old_certificate :
    theoremCode (certificate old_output_edge_is_old) =
      imp fullNoGarbage.encode (imp suffixClean.encode
        (imp (filterGraph 45 40 35 (neg (member 32 35))) (imp (member 32 5)
          (imp competitorPairs.encode (imp (member 64 63) (member 10 63)))))) :=
  certificate_correct old_output_edge_is_old
end PASoundness.PAtoCompactMultiplicationFullPrefixOldEdge
#print axioms PASoundness.PAtoCompactMultiplicationFullPrefixOldEdge.old_output_edge_is_old
#print axioms PASoundness.PAtoCompactMultiplicationFullPrefixOldEdge.old_output_edge_is_old_certificate
