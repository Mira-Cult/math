import PASoundness.PAtoCompactSuffixBoundaryPoint
import PASoundness.PAtoCompactBijectionForwardAtSeven
import PASoundness.PAtoCompactBijectionVacuity
import PASoundness.PAtoCompactOrderIsoVacuity
import PASoundness.PAtoCompactRestrictionSubset
import PASoundness.PAtoCompactRestrictionEdgeRetainClosed
import PASoundness.PAtoCompactRestrictionEdgeReverseClosed
import PASoundness.PAtoCompactRestrictionFresh19
import PASoundness.PAtoCompactRestrictionFilterVacuity
import PASoundness.PAtoCompactTransitiveWitness

/-! Forward coverage for a supplied restriction of the same isomorphism
 graph to two actual relative-complement suffixes. The original bijection,
 order, cut memberships, cut edge, both suffix filters and graph filter are
 explicit hypotheses. This constructs neither the cut nor any graph, and
 proves no reverse coverage, isomorphism, or addition output transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixGraphForwardCoverage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactBijectionForwardAtSeven
open PASoundness.PAtoCompactBijectionVacuity PASoundness.PAtoCompactOrderIsoVacuity
open PASoundness.PAtoCompactRestrictionSubset PASoundness.PAtoCompactRestrictionFresh19
open PASoundness.PAtoCompactRestrictionFilterVacuity PASoundness.PAtoCompactSuffixBoundaryPoint
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Endpoint restriction of the original graph6 to suffixes40 and41. -/
def graphFilter : Nat := filterGraph 6 8 14 (edgePredicate 14 40 41).encode

private def sourceFilterNamed : Formula :=
  .all 42 (namedFilterBody 0 40 42 (Formula.member 2 42).not)
private def targetFilterNamed : Formula :=
  .all 43 (namedFilterBody 1 41 43 (Formula.member 5 43).not)
private theorem source_filter_code : sourceFilterNamed.encode = sourceFilter := by rfl
private theorem target_filter_code : targetFilterNamed.encode = targetFilter := by rfl

/-- Full forward witness for source suffix member 7 and the same selected
image 3, now in target suffix41 with edge in restricted graph8. -/
def suffixForwardWitness : Formula := namedBoth (.member 41 3)
  (namedBoth (graphFormula 8 7 3) (.all 4
    (.imp (namedBoth (.member 41 4) (graphFormula 8 7 4)) (.equal 4 3))))

/-- Any competing suffix edge is an original edge with target in outer1.
This uses target suffix containment from the actual filter, not a false
assumption that suffix41 is a member of outer1. -/
def suffix_guard_to_original : KDerivation
    (imp targetFilter (imp graphFilter
      (allCode 4 (imp (both (member 41 4) (graphFormula 8 7 4).encode)
        (both (member 1 4) (graphFormula 6 7 4).encode))))) := by
  let G := targetFilter
  let F := graphFilter
  let A := both (member 41 4) (graphFormula 8 7 4).encode
  let B := both (member 1 4) (graphFormula 6 7 4).encode
  let Γ := [F,G]
  have hpoint : Context Γ (imp A B) := by
    apply Context.deduction
    let Δ := A :: Γ
    have ha : Context Δ A := .head _ _
    have hm : Context Δ (member 41 4) := Context.conjunctionLeft ha
    have he : Context Δ (graphFormula 8 7 4).encode := Context.conjunctionRight ha
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have hg : Context Δ G := .hypothesis (by simp [Δ,Γ])
    have hm' : Context Δ (member 1 4) :=
      .mp hm (.mp hg (.closed (filter_member_source 1 41 43
        (neg (member 5 43)) 4 (by decide) (by decide) (by decide))))
    have h19 : 19 ∉ (namedFilter 6 8 14 40 41).names :=
      filter_fresh_19 6 8 14 40 41 (by decide)
    have he' : Context Δ (graphFormula 6 7 4).encode :=
      .mp he (.mp hf (.closed
        (PAtoCompactRestrictionEdgeReverseClosed.restricted_edge_source
          6 8 14 40 41 7 4 (by decide) (by decide) (by decide) h19)))
    exact Context.conjunctionIntro hm' he'
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 4 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases hf : z = F
    · subst z
      simpa only [F, graphFilter] using
        (restriction_filter_vacuity 6 8 14 40 41 4 (by decide))
    have hg : z = G := by simp_all
    subst z
    simpa only [G, ← target_filter_code] using (targetFilterNamed.vacuity 4 (by decide))
  have hall : Context Γ (allCode 4 (imp A B)) := Context.generalize 4 hv hpoint
  exact Context.closeEmpty (Context.deduction (Context.deduction hall))

/-- An original forward witness and the same selected restricted edge give
full uniqueness in the suffix graph. -/
def suffix_witness_from_original : KDerivation
    (imp targetFilter (imp graphFilter (imp witnessAtSeven.encode
      (imp (both (member 41 3) (graphFormula 8 7 3).encode)
        suffixForwardWitness.encode)))) := by
  let G := targetFilter
  let F := graphFilter
  let W := witnessAtSeven.encode
  let R := both (member 41 3) (graphFormula 8 7 3).encode
  let A := both (member 41 4) (graphFormula 8 7 4).encode
  let B := both (member 1 4) (graphFormula 6 7 4).encode
  let C := equal 4 3
  have hcomp : KDerivation (imp (imp A B) (imp (imp B C) (imp A C))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Δ := [A,imp B C,imp A B]
    have ha : Context Δ A := .head _ _
    have hab : Context Δ (imp A B) := .hypothesis (by simp [Δ])
    have hbc : Context Δ (imp B C) := .hypothesis (by simp [Δ])
    exact .mp (.mp ha hab) hbc
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [R,W,F,G]
  have hr : Context Γ R := .head _ _
  have hw : Context Γ W := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hguard : Context Γ (allCode 4 (imp A B)) :=
    .mp hf (.mp hg (.closed suffix_guard_to_original))
  have hu : Context Γ (allCode 4 (imp B C)) :=
    Context.conjunctionRight (Context.conjunctionRight hw)
  have htrans : Context Γ (allCode 4 (imp (imp B C) (imp A C))) :=
    Context.allMP hguard (.closed (.generalize 4 hcomp))
  have hnew : Context Γ (allCode 4 (imp A C)) := Context.allMP hu htrans
  have hm : Context Γ (member 41 3) := Context.conjunctionLeft hr
  have he : Context Γ (graphFormula 8 7 3).encode := Context.conjunctionRight hr
  simpa only [Γ, R, W, F, G, A, C, suffixForwardWitness, namedBoth, Formula.not,
    Formula.encode, CompactProof.both, CompactProof.neg] using
      Context.conjunctionIntro hm (Context.conjunctionIntro he hnew)

/-- Every supplied source suffix member has an image in the target suffix
in the supplied restricted graph, retaining uniqueness from the original
bijection. The same original graph6 supplies both the selected cut edge and
the source-image edge. Syntactic labels are fixed; denoted values may alias. -/
def suffix_forward_witness_exists : KDerivation
    (imp orderFormula.encode (imp sourceFilter (imp targetFilter
      (imp (member 0 2) (imp (member 1 5) (imp (graphFormula 6 2 5).encode
        (imp bijectionFormula.encode (imp graphFilter (imp (member 40 7)
          (existsCode 3 suffixForwardWitness.encode)))))))))) := by
  let O := orderFormula.encode
  let S := sourceFilter
  let T := targetFilter
  let C := member 0 2
  let D := member 1 5
  let E := (graphFormula 6 2 5).encode
  let B := bijectionFormula.encode
  let F := graphFilter
  let L := member 40 7
  let W := witnessAtSeven.encode
  let Γ := [L,F,B,E,D,C,T,S,O]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 3 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases h : z = L
    · subst z; exact membershipVacuity 40 7 3 (by decide) (by decide)
    by_cases h : z = F
    · subst z; simpa only [F,graphFilter] using
        (restriction_filter_vacuity 6 8 14 40 41 3 (by decide))
    by_cases h : z = B
    · subst z; exact bijection_vacuity_three
    by_cases h : z = E
    · subst z; exact (graphFormula 6 2 5).vacuity 3 (by decide)
    by_cases h : z = D
    · subst z; exact membershipVacuity 1 5 3 (by decide) (by decide)
    by_cases h : z = C
    · subst z; exact membershipVacuity 0 2 3 (by decide) (by decide)
    by_cases h : z = T
    · subst z; simpa only [T, ← target_filter_code] using (targetFilterNamed.vacuity 3 (by decide))
    by_cases h : z = S
    · subst z; simpa only [S, ← source_filter_code] using (sourceFilterNamed.vacuity 3 (by decide))
    have h : z = O := by simp_all
    subst z
    exact order_vacuity 3 order_fresh_3
  have hlocal : Context Γ (imp W suffixForwardWitness.encode) := by
    apply Context.deduction
    let Δ := W :: Γ
    have hw : Context Δ W := .head _ _
    have hm : Context Δ (member 1 3) := Context.conjunctionLeft hw
    have hedge : Context Δ (graphFormula 6 7 3).encode := Context.conjunctionLeft (Context.conjunctionRight hw)
    have hl : Context Δ L := .hypothesis (by simp [Δ,Γ])
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have he : Context Δ E := .hypothesis (by simp [Δ,Γ])
    have hd : Context Δ D := .hypothesis (by simp [Δ,Γ])
    have hc : Context Δ C := .hypothesis (by simp [Δ,Γ])
    have ht : Context Δ T := .hypothesis (by simp [Δ,Γ])
    have hs : Context Δ S := .hypothesis (by simp [Δ,Γ])
    have ho : Context Δ O := .hypothesis (by simp [Δ,Γ])
    have hsource : Context Δ (member 0 7) :=
      .mp hl (.mp hs (.closed (filter_member_source 0 40 42
        (neg (member 2 42)) 7 (by decide) (by decide) (by decide))))
    have hboundary : Context Δ (both (imp L (member 41 3)) (imp (member 41 3) L)) :=
      .mp he (.mp hedge (.mp hd (.mp hm (.mp hc (.mp hsource (.mp ht (.mp hs
        (.mp ho (.closed suffix_boundary_point)))))))))
    have htarget : Context Δ (member 41 3) := .mp hl (Context.conjunctionLeft hboundary)
    have hnew : Context Δ (graphFormula 8 7 3).encode :=
      .mp hedge (.mp htarget (.mp hl (.mp hf (.closed
        (PAtoCompactRestrictionEdgeRetainClosed.retain_edge 6 8 14 40 41 7 3 (by decide))))))
    have hpair : Context Δ (both (member 41 3) (graphFormula 8 7 3).encode) :=
      Context.conjunctionIntro htarget hnew
    exact .mp hpair (.mp hw (.mp hf (.mp ht (.closed suffix_witness_from_original))))
  have hex : Context Γ (existsCode 3 W) := by
    have hl : Context Γ L := .head _ _
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have hsource : Context Γ (member 0 7) :=
      .mp hl (.mp hs (.closed (filter_member_source 0 40 42
        (neg (member 2 42)) 7 (by decide) (by decide) (by decide))))
    exact .mp hsource (.mp hb (.closed forward_witness_at_seven))
  have hres : Context Γ (existsCode 3 suffixForwardWitness.encode) :=
    exists_map_context (Context.generalize 3 hv hlocal) hex
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
  exact hres

theorem suffix_forward_witness_exists_certificate :
    theoremCode (certificate suffix_forward_witness_exists) =
      imp orderFormula.encode (imp sourceFilter (imp targetFilter
        (imp (member 0 2) (imp (member 1 5) (imp (graphFormula 6 2 5).encode
          (imp bijectionFormula.encode (imp graphFilter (imp (member 40 7)
            (existsCode 3 suffixForwardWitness.encode))))))))) :=
  certificate_correct suffix_forward_witness_exists

end PASoundness.PAtoCompactSuffixGraphForwardCoverage

#print axioms PASoundness.PAtoCompactSuffixGraphForwardCoverage.graphFilter
#print axioms PASoundness.PAtoCompactSuffixGraphForwardCoverage.suffixForwardWitness
#print axioms PASoundness.PAtoCompactSuffixGraphForwardCoverage.suffix_guard_to_original
#print axioms PASoundness.PAtoCompactSuffixGraphForwardCoverage.suffix_witness_from_original
#print axioms PASoundness.PAtoCompactSuffixGraphForwardCoverage.suffix_forward_witness_exists
#print axioms PASoundness.PAtoCompactSuffixGraphForwardCoverage.suffix_forward_witness_exists_certificate
