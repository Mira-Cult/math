import PASoundness.PAtoCompactSuffixGraphReverseCoverage
import PASoundness.PAtoCompactBijectionVacuity
import PASoundness.PAtoCompactOrderIsoVacuity

/-! Quantified reverse coverage for the same supplied suffix graph. This
constructs neither the graph nor a complete suffix isomorphism. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixGraphReverseAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuffixBoundaryPoint PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactRestrictionFilterVacuity PASoundness.PAtoCompactBijectionVacuity
open PASoundness.PAtoCompactOrderIsoVacuity PASoundness.PAtoCompactSuffixGraphReverseRetained
open PASoundness.PAtoCompactSuffixGraphReverseCoverage
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def namedSourceFilter : Formula := .all 42
  (namedFilterBody 0 40 42 ((Formula.member 2 42).not))
private def namedTargetFilter : Formula := .all 43
  (namedFilterBody 1 41 43 ((Formula.member 5 43).not))
private theorem source_filter_code : namedSourceFilter.encode = sourceFilter := by
  simp [namedSourceFilter,namedFilterBody,namedBoth,sourceFilter,filterGraph,
    filterPredicate,Formula.not,Formula.encode,CompactProof.both,CompactProof.neg]
private theorem target_filter_code : namedTargetFilter.encode = targetFilter := by
  simp [namedTargetFilter,namedFilterBody,namedBoth,targetFilter,filterGraph,
    filterPredicate,Formula.not,Formula.encode,CompactProof.both,CompactProof.neg]

/-- All target-suffix members have unique source-suffix preimages on the
same supplied filtered graph. The original graph and order/bijection matrices,
cut edge and membership guards, and all three filters remain explicit.
Syntactic names are fixed; denoted objects may coincide. -/
def suffix_reverse_all : KDerivation
    (imp orderFormula.encode (imp bijectionFormula.encode
      (imp sourceFilter (imp targetFilter (imp graphFilter
        (imp (member 0 2) (imp (member 1 5) (imp (graphFormula 6 2 5).encode
          (allCode 3 (imp (member 41 3) (existsCode 7 suffixReverseWitness.encode))))))))))) := by
  let O := orderFormula.encode
  let B := bijectionFormula.encode
  let F := sourceFilter
  let G := targetFilter
  let H := graphFilter
  let A := member 0 2
  let D := member 1 5
  let E := (graphFormula 6 2 5).encode
  let V := member 41 3
  let R := existsCode 7 suffixReverseWitness.encode
  let Γ := [E,D,A,H,G,F,B,O]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 3 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases he : z = E
    · subst z; exact (graphFormula 6 2 5).vacuity 3 (by decide)
    by_cases he : z = D
    · subst z; exact membershipVacuity 1 5 3 (by decide) (by decide)
    by_cases he : z = A
    · subst z; exact membershipVacuity 0 2 3 (by decide) (by decide)
    by_cases he : z = H
    · subst z
      simpa only [H,graphFilter] using
        (restriction_filter_vacuity 6 8 14 40 41 3 (by decide))
    by_cases he : z = G
    · subst z
      simpa only [G, ← target_filter_code] using (namedTargetFilter.vacuity 3 (by decide))
    by_cases he : z = F
    · subst z
      simpa only [F, ← source_filter_code] using (namedSourceFilter.vacuity 3 (by decide))
    by_cases he : z = B
    · subst z; exact bijection_vacuity_three
    have he : z = O := by simp_all
    subst z
    exact order_vacuity 3 order_fresh_3
  have hlocal : Context Γ (imp V R) := by
    apply Context.deduction
    let Δ := V :: Γ
    have hv : Context Δ V := .head _ _
    have he : Context Δ E := .hypothesis (by simp [Δ,Γ])
    have hd : Context Δ D := .hypothesis (by simp [Δ,Γ])
    have ha : Context Δ A := .hypothesis (by simp [Δ,Γ])
    have hh : Context Δ H := .hypothesis (by simp [Δ,Γ])
    have hg : Context Δ G := .hypothesis (by simp [Δ,Γ])
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have hb : Context Δ B := .hypothesis (by simp [Δ,Γ])
    have ho : Context Δ O := .hypothesis (by simp [Δ,Γ])
    exact .mp hv (.mp he (.mp hd (.mp ha (.mp hh (.mp hg (.mp hf (.mp hb
      (.mp ho (.closed suffix_reverse_coverage)))))))))
  have hall : Context Γ (allCode 3 (imp V R)) := Context.generalize 3 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hall

theorem suffix_reverse_all_certificate : theoremCode (certificate suffix_reverse_all) =
    imp orderFormula.encode (imp bijectionFormula.encode
      (imp sourceFilter (imp targetFilter (imp graphFilter
        (imp (member 0 2) (imp (member 1 5) (imp (graphFormula 6 2 5).encode
          (allCode 3 (imp (member 41 3) (existsCode 7 suffixReverseWitness.encode)))))))))) :=
  certificate_correct suffix_reverse_all

end PASoundness.PAtoCompactSuffixGraphReverseAll

#print axioms PASoundness.PAtoCompactSuffixGraphReverseAll.suffix_reverse_all
#print axioms PASoundness.PAtoCompactSuffixGraphReverseAll.suffix_reverse_all_certificate
