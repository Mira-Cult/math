import PASoundness.PAtoCompactSuffixBoundaryPoint
import PASoundness.PAtoCompactTransitiveWitness
import PASoundness.PAtoCompactBijectionBackwardAtThree
import PASoundness.PAtoCompactRestrictionEdgeEquivalence
import PASoundness.PAtoCompactRestrictionFilterVacuity

/-! Reverse coverage for a supplied endpoint-filtered graph between two
proper-cut suffixes. The selected preimage retains its original full
bijection witness, so later uniqueness can use the SAME source element.
This does not construct a graph or prove a complete suffix isomorphism. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixGraphReverseRetained
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuffixBoundaryPoint PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactRestrictionFilterVacuity PASoundness.PAtoCompactRestrictionEdgeEquivalence
open PASoundness.PAtoCompactBijectionBackwardAtThree
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Graph 8 is the restriction of original graph 6 to suffixes 40 and 41. -/
def graphFilter : Nat := filterGraph 6 8 14 (edgePredicate 14 40 41).encode

/-- Retain the complete original preimage witness, the source suffix membership,
and the corresponding edge in the restricted graph, under one name 7. -/
def retainedWitness : Formula := namedBoth (witness 7)
  (namedBoth (.member 40 7) (graphFormula 8 7 3))

private def namedSourceFilter : Formula := .all 42
  (namedFilterBody 0 40 42 ((Formula.member 2 42).not))
private def namedTargetFilter : Formula := .all 43
  (namedFilterBody 1 41 43 ((Formula.member 5 43).not))

private theorem source_filter_code : namedSourceFilter.encode = sourceFilter := by
  simp [namedSourceFilter, namedFilterBody, namedBoth, sourceFilter, filterGraph,
    filterPredicate, Formula.not, Formula.encode, CompactProof.both, CompactProof.neg]
private theorem target_filter_code : namedTargetFilter.encode = targetFilter := by
  simp [namedTargetFilter, namedFilterBody, namedBoth, targetFilter, filterGraph,
    filterPredicate, Formula.not, Formula.encode, CompactProof.both, CompactProof.neg]

private def target_suffix_outer : KDerivation
    (imp targetFilter (imp (member 41 3) (member 1 3))) := by
  let P : Formula := (Formula.member 5 43).not
  have h := filter_at 1 41 43 3 P (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have ht : KDerivation (imp targetFilter
      (both (imp (member 41 3) (both (member 1 3) (neg (member 5 3))))
        (imp (both (member 1 3) (neg (member 5 3))) (member 41 3)))) := by
    simpa [P, targetFilter, Formula.not, Formula.encode, replace, rename, neg] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 41 3,targetFilter]
  have hv : Context Γ (member 41 3) := .head _ _
  have hf : Context Γ targetFilter := .hypothesis (by simp [Γ])
  exact Context.conjunctionLeft (.mp hv (Context.conjunctionLeft (.mp hf (.closed ht))))

/-- Every supplied target-suffix member has a source-suffix preimage in the
supplied filtered graph. The preimage's original graph witness, including its
original uniqueness clause, is retained under the same existential. Both
cut-membership guards and the actual selected cut edge remain explicit.
The fixed labels are syntactic; their denoted objects may coincide. -/
def reverse_retained : KDerivation
    (imp orderFormula.encode (imp bijectionFormula.encode
      (imp sourceFilter (imp targetFilter (imp graphFilter
        (imp (member 0 2) (imp (member 1 5) (imp (graphFormula 6 2 5).encode
          (imp (member 41 3) (existsCode 7 retainedWitness.encode)))))))))) := by
  let O := orderFormula.encode
  let B := bijectionFormula.encode
  let F := sourceFilter
  let G := targetFilter
  let H := graphFilter
  let A := member 0 2
  let D := member 1 5
  let E := (graphFormula 6 2 5).encode
  let V := member 41 3
  let W := (witness 7).encode
  let R := retainedWitness.encode
  let Γ := [V,E,D,A,H,G,F,B,O]
  have hctx : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 7 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases he : z = V
    · subst z; exact membershipVacuity 41 3 7 (by decide) (by decide)
    by_cases he : z = E
    · subst z; exact (graphFormula 6 2 5).vacuity 7 (by decide)
    by_cases he : z = D
    · subst z; exact membershipVacuity 1 5 7 (by decide) (by decide)
    by_cases he : z = A
    · subst z; exact membershipVacuity 0 2 7 (by decide) (by decide)
    by_cases he : z = H
    · subst z
      simpa only [H, graphFilter] using
        (restriction_filter_vacuity 6 8 14 40 41 7 (by decide))
    by_cases he : z = G
    · subst z
      simpa only [G, ← target_filter_code] using
        (namedTargetFilter.vacuity 7 (by decide))
    by_cases he : z = F
    · subst z
      simpa only [F, ← source_filter_code] using
        (namedSourceFilter.vacuity 7 (by decide))
    by_cases he : z = B
    · subst z; exact bijectionFormula.vacuity 7 (by decide)
    have he : z = O := by simp_all
    subst z
    exact orderFormula.vacuity 7 (by decide)
  have houtside : Context Γ (member 1 3) := by
    have hg : Context Γ G := .hypothesis (by simp [Γ])
    have hv : Context Γ V := .head _ _
    exact .mp hv (.mp hg (.closed target_suffix_outer))
  have hex : Context Γ (existsCode 7 W) := by
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    exact .mp houtside (.mp hb (.closed backward_witness))
  have hlocal : Context Γ (imp W R) := by
    apply Context.deduction
    let Δ := W :: Γ
    have hw : Context Δ W := .head _ _
    have hs : Context Δ (member 0 7) := Context.conjunctionLeft hw
    have he : Context Δ (graphFormula 6 7 3).encode :=
      Context.conjunctionLeft (Context.conjunctionRight hw)
    have ht : Context Δ (member 1 3) := Context.under houtside W
    have ho : Context Δ O := .hypothesis (by simp [Δ,Γ])
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have hg : Context Δ G := .hypothesis (by simp [Δ,Γ])
    have hh : Context Δ H := .hypothesis (by simp [Δ,Γ])
    have ha : Context Δ A := .hypothesis (by simp [Δ,Γ])
    have hd : Context Δ D := .hypothesis (by simp [Δ,Γ])
    have hecut : Context Δ E := .hypothesis (by simp [Δ,Γ])
    have hv : Context Δ V := .hypothesis (by simp [Δ,Γ])
    have hboundary : Context Δ (both (imp (member 40 7) V) (imp V (member 40 7))) :=
      .mp hecut (.mp he (.mp hd (.mp ht (.mp ha (.mp hs (.mp hg (.mp hf
        (.mp ho (.closed suffix_boundary_point)))))))))
    have hsrc : Context Δ (member 40 7) := .mp hv (Context.conjunctionRight hboundary)
    have hiff : Context Δ (both (imp (graphFormula 6 7 3).encode (graphFormula 8 7 3).encode)
        (imp (graphFormula 8 7 3).encode (graphFormula 6 7 3).encode)) :=
      .mp hv (.mp hsrc (.mp hh (.closed (restricted_edge_iff 6 8 14 40 41 7 3 (by decide)))))
    have hedge : Context Δ (graphFormula 8 7 3).encode := .mp he (Context.conjunctionLeft hiff)
    simpa only [R, retainedWitness, namedBoth, Formula.not, Formula.encode,
      CompactProof.both, CompactProof.neg] using
      Context.conjunctionIntro hw (Context.conjunctionIntro hsrc hedge)
  have hresult : Context Γ (existsCode 7 R) :=
    PAtoCompactTransitiveWitness.exists_map_context (Context.generalize 7 hctx hlocal) hex
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
  exact hresult

theorem reverse_retained_certificate : theoremCode (certificate reverse_retained) =
    imp orderFormula.encode (imp bijectionFormula.encode
      (imp sourceFilter (imp targetFilter (imp graphFilter
        (imp (member 0 2) (imp (member 1 5) (imp (graphFormula 6 2 5).encode
          (imp (member 41 3) (existsCode 7 retainedWitness.encode))))))))) :=
  certificate_correct reverse_retained

end PASoundness.PAtoCompactSuffixGraphReverseRetained

#print axioms PASoundness.PAtoCompactSuffixGraphReverseRetained.graphFilter
#print axioms PASoundness.PAtoCompactSuffixGraphReverseRetained.retainedWitness
#print axioms PASoundness.PAtoCompactSuffixGraphReverseRetained.reverse_retained
#print axioms PASoundness.PAtoCompactSuffixGraphReverseRetained.reverse_retained_certificate
