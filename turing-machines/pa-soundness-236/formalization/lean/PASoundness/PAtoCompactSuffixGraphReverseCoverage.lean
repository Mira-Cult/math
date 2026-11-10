import PASoundness.PAtoCompactSuffixGraphReverseRetained
import PASoundness.PAtoCompactTransitiveWitness
import PASoundness.PAtoCompactSuffixReverseUnique

/-! Assemble a full reverse-bijection witness for the supplied suffix graph.
The retained original witness and its filtered uniqueness share one source
name; graph construction and universal reverse coverage are separate. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixGraphReverseCoverage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuffixBoundaryPoint PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactRestrictionFilterVacuity PASoundness.PAtoCompactBijectionBackwardAtThree
open PASoundness.PAtoCompactSuffixGraphReverseRetained
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Literal reverse-bijection witness for target 3, selected source 7,
source suffix 40, restricted graph 8, competing source name 4. -/
def suffixReverseWitness : Formula := namedBoth (.member 40 7)
  (namedBoth (graphFormula 8 7 3) (.all 4
    (.imp (namedBoth (.member 40 4) (graphFormula 8 4 3)) (.equal 4 7))))

private def namedSourceFilter : Formula := .all 42
  (namedFilterBody 0 40 42 ((Formula.member 2 42).not))
private theorem source_filter_code : namedSourceFilter.encode = sourceFilter := by
  simp [namedSourceFilter, namedFilterBody, namedBoth, sourceFilter, filterGraph,
    filterPredicate, Formula.not, Formula.encode, CompactProof.both, CompactProof.neg]

/-- Preserve the selected preimage while strengthening the retained source
and edge with uniqueness in the restricted graph. The original witness is
used only inside the proof, and all objects denoted by labels may coincide. -/
def retained_to_reverse : KDerivation
    (imp sourceFilter (imp graphFilter (imp (existsCode 7 retainedWitness.encode)
      (existsCode 7 suffixReverseWitness.encode)))) := by
  let F := sourceFilter
  let H := graphFilter
  let W := retainedWitness.encode
  let R := suffixReverseWitness.encode
  let Γ := [H,F]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 7 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases he : z = H
    · subst z
      simpa only [H,graphFilter] using
        (restriction_filter_vacuity 6 8 14 40 41 7 (by decide))
    have he : z = F := by simp_all
    subst z
    simpa only [F, ← source_filter_code] using (namedSourceFilter.vacuity 7 (by decide))
  have hlocal : Context Γ (imp W R) := by
    apply Context.deduction
    let Δ := W :: Γ
    have hw : Context Δ W := .head _ _
    have hold : Context Δ (witness 7).encode := Context.conjunctionLeft hw
    have hseg : Context Δ (both (member 40 7) (graphFormula 8 7 3).encode) :=
      Context.conjunctionRight hw
    have hs : Context Δ (member 40 7) := Context.conjunctionLeft hseg
    have he : Context Δ (graphFormula 8 7 3).encode := Context.conjunctionRight hseg
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have hh : Context Δ H := .hypothesis (by simp [Δ,Γ])
    have hu : Context Δ (allCode 4
        (imp (both (member 40 4) (graphFormula 8 4 3).encode) (equal 4 7))) := by
      have h := PAtoCompactSuffixReverseUnique.suffix_reverse_unique
      exact .mp hold (.mp hh (.mp hf (.closed h)))
    simpa only [R,suffixReverseWitness,namedBoth,Formula.not,Formula.encode,
      CompactProof.both,CompactProof.neg] using
      Context.conjunctionIntro hs (Context.conjunctionIntro he hu)
  have hall : Context Γ (allCode 7 (imp W R)) := Context.generalize 7 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Δ := [existsCode 7 W,H,F]
  have he : Context Δ (existsCode 7 W) := .head _ _
  have hall' : Context Δ (allCode 7 (imp W R)) := Context.under hall _
  exact PAtoCompactTransitiveWitness.exists_map_context hall' he

/-- For every supplied target-suffix member, K produces a full reverse
bijection witness in the restricted graph, under all explicit original graph,
cut, suffix-filter and endpoint-filter assumptions. This is pointwise in 3;
no graph existence or quantified reverse clause is claimed. -/
def suffix_reverse_coverage : KDerivation
    (imp orderFormula.encode (imp bijectionFormula.encode
      (imp sourceFilter (imp targetFilter (imp graphFilter
        (imp (member 0 2) (imp (member 1 5) (imp (graphFormula 6 2 5).encode
          (imp (member 41 3) (existsCode 7 suffixReverseWitness.encode)))))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let O := orderFormula.encode
  let B := bijectionFormula.encode
  let F := sourceFilter
  let G := targetFilter
  let H := graphFilter
  let A := member 0 2
  let D := member 1 5
  let E := (graphFormula 6 2 5).encode
  let V := member 41 3
  let Γ := [V,E,D,A,H,G,F,B,O]
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hv : Context Γ V := .head _ _
  have hw : Context Γ (existsCode 7 retainedWitness.encode) :=
    .mp hv (.mp he (.mp hd (.mp ha (.mp hh (.mp hg (.mp hf (.mp hb
      (.mp ho (.closed reverse_retained)))))))))
  exact .mp hw (.mp hh (.mp hf (.closed retained_to_reverse)))

theorem suffix_reverse_coverage_certificate :
    theoremCode (certificate suffix_reverse_coverage) =
      imp orderFormula.encode (imp bijectionFormula.encode
        (imp sourceFilter (imp targetFilter (imp graphFilter
          (imp (member 0 2) (imp (member 1 5) (imp (graphFormula 6 2 5).encode
            (imp (member 41 3) (existsCode 7 suffixReverseWitness.encode))))))))) :=
  certificate_correct suffix_reverse_coverage

end PASoundness.PAtoCompactSuffixGraphReverseCoverage

#print axioms PASoundness.PAtoCompactSuffixGraphReverseCoverage.suffixReverseWitness
#print axioms PASoundness.PAtoCompactSuffixGraphReverseCoverage.retained_to_reverse
#print axioms PASoundness.PAtoCompactSuffixGraphReverseCoverage.suffix_reverse_coverage
#print axioms PASoundness.PAtoCompactSuffixGraphReverseCoverage.suffix_reverse_coverage_certificate
