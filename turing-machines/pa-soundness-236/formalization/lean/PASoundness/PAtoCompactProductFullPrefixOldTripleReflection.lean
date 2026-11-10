import PASoundness.PAtoCompactProductTripleReflectionLift
import PASoundness.PAtoCompactMultiplicationFullPrefixOldEdge
import PASoundness.PAtoCompactProductOldCompetitorEndpoints

/-! Under the actual full-prefix no-garbage invariant, clean suffix map, and
literal suffix filter, a new-graph triple with an old-result output was
already an old-graph triple. The same inner pair and outer graph-member
witnesses are retained. The optional endpoint conclusion also assumes the old
graph is clean. This is not the full reverse product clause or totality. -/
namespace PASoundness.PAtoCompactProductFullPrefixOldTripleReflection
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactProductTripleReflectionLift
open PASoundness.PAtoCompactMultiplicationFullPrefixOldEdge
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactMultiplicationRowQueryCompetitor
open PASoundness.PAtoCompactProductOldSuffixExclusion
open PASoundness.PAtoCompactProductOldCompetitorEndpoints
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def filter : Formula := .all 35
  (namedFilterBody 45 40 35 (Formula.member 32 35).not)
/-- Full-prefix row no-garbage, clean suffix map, exact filter, and the
queried output's old-result membership. -/
def hypotheses : Formula := namedBoth fullNoGarbage
  (namedBoth suffixClean (namedBoth filter (.member 32 5)))
private theorem filter_code : filter.encode = filterGraph 45 40 35 (neg (member 32 35)) := by rfl
private theorem pairs_match : competitorPairs = queryPairs := by decide

private def edge_reflection : KDerivation (imp hypotheses.encode
    (imp queryPairs.encode (imp (member 64 63) (member 10 63)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 64 63,queryPairs.encode,hypotheses.encode]
  have he : Context Γ (member 64 63) := .head _ _
  have hq : Context Γ queryPairs.encode := .hypothesis (by simp [Γ])
  have hh : Context Γ hypotheses.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ (both fullNoGarbage.encode (both suffixClean.encode
      (both (filterGraph 45 40 35 (neg (member 32 35))) (member 32 5)))) := by
    simpa [hypotheses,filter_code,namedBoth,Formula.not,Formula.encode,both,neg] using hh
  have hn := Context.conjunctionLeft hp
  have hc := Context.conjunctionLeft (Context.conjunctionRight hp)
  have hf := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hp))
  have ho := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hp))
  have hq' : Context Γ competitorPairs.encode := by simpa only [pairs_match] using hq
  exact .mp he (.mp hq' (.mp ho (.mp hf (.mp hc (.mp hn (.closed old_output_edge_is_old))))))

/-- A queried new-graph triple at an old-result output is an old-graph triple,
under the explicit same-witness row and suffix conditions. -/
def old_output_triple_reflect : KDerivation (imp hypotheses.encode
    (imp (triple 64).encode (triple 10).encode)) :=
  triple_reflection_of_edge hypotheses (by decide) (by decide) edge_reflection

private theorem old_triple_match : triple 10 = oldCompetitor := by decide
/-- If the original graph is also clean, the reflected triple's input and
output values lie in their original domains. -/
def old_output_triple_endpoints : KDerivation (imp hypotheses.encode
    (imp oldClean.encode (imp (triple 64).encode
      (both (triple 10).encode competitorEndpoints.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(triple 64).encode,oldClean.encode,hypotheses.encode]
  have ht : Context Γ (triple 64).encode := .head _ _
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have hh : Context Γ hypotheses.encode := .hypothesis (by simp [Γ])
  have ho : Context Γ (triple 10).encode := .mp ht (.mp hh (.closed old_output_triple_reflect))
  have he : Context Γ competitorEndpoints.encode := by
    have ho' : Context Γ oldCompetitor.encode := by simpa only [old_triple_match] using ho
    exact .mp ho' (.mp hc (.closed competitor_endpoints))
  exact Context.conjunctionIntro ho he

theorem old_output_triple_reflect_certificate : theoremCode (certificate old_output_triple_reflect) =
    imp hypotheses.encode (imp (triple 64).encode (triple 10).encode) :=
  certificate_correct old_output_triple_reflect

theorem old_output_triple_endpoints_certificate : theoremCode (certificate old_output_triple_endpoints) =
    imp hypotheses.encode (imp oldClean.encode (imp (triple 64).encode
      (both (triple 10).encode competitorEndpoints.encode))) :=
  certificate_correct old_output_triple_endpoints
end PASoundness.PAtoCompactProductFullPrefixOldTripleReflection
#print axioms PASoundness.PAtoCompactProductFullPrefixOldTripleReflection.old_output_triple_reflect
#print axioms PASoundness.PAtoCompactProductFullPrefixOldTripleReflection.old_output_triple_endpoints
#print axioms PASoundness.PAtoCompactProductFullPrefixOldTripleReflection.old_output_triple_reflect_certificate
#print axioms PASoundness.PAtoCompactProductFullPrefixOldTripleReflection.old_output_triple_endpoints_certificate
