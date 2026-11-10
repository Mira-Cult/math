import PASoundness.PAtoCompactSuffixGraphForwardCoverage

/-! Quantified forward coverage and uniqueness in a supplied graph restricted
 to two proper-cut suffixes. The exact source isomorphism, cut and filter
 assumptions remain explicit; reverse coverage and graph construction are not
 asserted. All labels are syntactic and denoted values may coincide. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixGraphForwardAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactRestrictionFilterVacuity
open PASoundness.PAtoCompactSuffixBoundaryPoint PASoundness.PAtoCompactSuffixGraphForwardCoverage
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def sourceFilterNamed : Formula :=
  .all 42 (namedFilterBody 0 40 42 (Formula.member 2 42).not)
private def targetFilterNamed : Formula :=
  .all 43 (namedFilterBody 1 41 43 (Formula.member 5 43).not)
private theorem source_filter_code : sourceFilterNamed.encode = sourceFilter := by rfl
private theorem target_filter_code : targetFilterNamed.encode = targetFilter := by rfl

/-- Every member7 of suffix40 has a unique represented image in suffix41
on the supplied filtered graph8. The old graph6 and selected cut edge2→5
are the same throughout the displayed assumptions. -/
def suffix_forward_all : KDerivation
    (imp orderFormula.encode (imp sourceFilter (imp targetFilter
      (imp (member 0 2) (imp (member 1 5) (imp (graphFormula 6 2 5).encode
        (imp bijectionFormula.encode (imp graphFilter
          (allCode 7 (imp (member 40 7) (existsCode 3 suffixForwardWitness.encode))))))))))) := by
  let O := orderFormula.encode
  let S := sourceFilter
  let T := targetFilter
  let C := member 0 2
  let D := member 1 5
  let E := (graphFormula 6 2 5).encode
  let B := bijectionFormula.encode
  let F := graphFilter
  let Γ := [F,B,E,D,C,T,S,O]
  have hpoint : Context Γ (imp (member 40 7) (existsCode 3 suffixForwardWitness.encode)) := by
    have hf : Context Γ F := .head _ _
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have he : Context Γ E := .hypothesis (by simp [Γ])
    have hd : Context Γ D := .hypothesis (by simp [Γ])
    have hc : Context Γ C := .hypothesis (by simp [Γ])
    have ht : Context Γ T := .hypothesis (by simp [Γ])
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have ho : Context Γ O := .hypothesis (by simp [Γ])
    exact .mp hf (.mp hb (.mp he (.mp hd (.mp hc (.mp ht (.mp hs
      (.mp ho (.closed suffix_forward_witness_exists))))))))
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 7 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases h : z = F
    · subst z; simpa only [F,graphFilter] using
        (restriction_filter_vacuity 6 8 14 40 41 7 (by decide))
    by_cases h : z = B
    · subst z; exact bijectionFormula.vacuity 7 (by decide)
    by_cases h : z = E
    · subst z; exact (graphFormula 6 2 5).vacuity 7 (by decide)
    by_cases h : z = D
    · subst z; exact membershipVacuity 1 5 7 (by decide) (by decide)
    by_cases h : z = C
    · subst z; exact membershipVacuity 0 2 7 (by decide) (by decide)
    by_cases h : z = T
    · subst z; simpa only [T, ← target_filter_code] using (targetFilterNamed.vacuity 7 (by decide))
    by_cases h : z = S
    · subst z; simpa only [S, ← source_filter_code] using (sourceFilterNamed.vacuity 7 (by decide))
    have h : z = O := by simp_all
    subst z
    exact orderFormula.vacuity 7 (by decide)
  have hall : Context Γ (allCode 7 (imp (member 40 7) (existsCode 3 suffixForwardWitness.encode))) :=
    Context.generalize 7 hv hpoint
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

theorem suffix_forward_all_certificate : theoremCode (certificate suffix_forward_all) =
    imp orderFormula.encode (imp sourceFilter (imp targetFilter
      (imp (member 0 2) (imp (member 1 5) (imp (graphFormula 6 2 5).encode
        (imp bijectionFormula.encode (imp graphFilter
          (allCode 7 (imp (member 40 7) (existsCode 3 suffixForwardWitness.encode)))))))))) :=
  certificate_correct suffix_forward_all

end PASoundness.PAtoCompactSuffixGraphForwardAll

#print axioms PASoundness.PAtoCompactSuffixGraphForwardAll.suffix_forward_all
#print axioms PASoundness.PAtoCompactSuffixGraphForwardAll.suffix_forward_all_certificate
