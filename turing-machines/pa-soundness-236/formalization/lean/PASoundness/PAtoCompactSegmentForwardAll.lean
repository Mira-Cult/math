import PASoundness.PAtoCompactSegmentForwardExists

/-! Quantified K forward clause for an isomorphism restricted to arbitrary
initial segments. The graph filter, endpoint memberships, transitivity, old
isomorphism clauses and top edge remain explicit hypotheses. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentForwardAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactRestrictionFilterVacuity
open PASoundness.PAtoCompactRestrictedForwardPoint PASoundness.PAtoCompactRestrictedForwardUnique
open PASoundness.PAtoCompactSegmentForwardExists
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Every member of source segment 2 has the same unique filtered image in
segment 5, provided the explicitly supplied original graph is an order
isomorphism between outer domains and sends 2 to 5. -/
def segment_forward_all : KDerivation
    (imp (transitiveCode 0 11 12) (imp (transitiveCode 1 16 18)
      (imp (member 0 2) (imp (member 1 5)
        (imp orderFormula.encode (imp filter (imp (graphFormula 6 2 5).encode
          (imp bijectionFormula.encode (allCode 7 (imp (member 2 7)
            (existsCode 3 restrictedWitness.encode))))))))))) := by
  let T0 := transitiveCode 0 11 12
  let T1 := transitiveCode 1 16 18
  let M0 := member 0 2
  let M1 := member 1 5
  let O := orderFormula.encode
  let F := filter
  let Top := (graphFormula 6 2 5).encode
  let B := bijectionFormula.encode
  let A := member 2 7
  let E := existsCode 3 restrictedWitness.encode
  let Γ := [B,Top,F,O,M1,M0,T1,T0]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 7 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = B
    · subst z; exact bijectionFormula.vacuity 7 (by decide)
    by_cases he : z = Top
    · subst z; exact (graphFormula 6 2 5).vacuity 7 (by decide)
    by_cases he : z = F
    · subst z
      simpa only [F, filter] using (restriction_filter_vacuity 6 8 14 2 5 7 (by decide))
    by_cases he : z = O
    · subst z; exact orderFormula.vacuity 7 (by decide)
    by_cases he : z = M1
    · subst z; exact membershipVacuity 1 5 7 (by decide) (by decide)
    by_cases he : z = M0
    · subst z; exact membershipVacuity 0 2 7 (by decide) (by decide)
    by_cases he : z = T1
    · subst z; exact transitive_vacuity 1 16 18 7 (by decide) (by decide) (by decide)
    have he : z = T0 := by simp_all
    subst z
    exact transitive_vacuity 0 11 12 7 (by decide) (by decide) (by decide)
  have hpoint : Context Γ (imp A E) := by
    have hb : Context Γ B := .head _ _
    have htop : Context Γ Top := .hypothesis (by simp [Γ])
    have hf : Context Γ F := .hypothesis (by simp [Γ])
    have ho : Context Γ O := .hypothesis (by simp [Γ])
    have h1 : Context Γ M1 := .hypothesis (by simp [Γ])
    have h0 : Context Γ M0 := .hypothesis (by simp [Γ])
    have ht1 : Context Γ T1 := .hypothesis (by simp [Γ])
    have ht0 : Context Γ T0 := .hypothesis (by simp [Γ])
    exact .mp hb (.mp htop (.mp hf (.mp ho (.mp h1 (.mp h0 (.mp ht1
      (.mp ht0 (.closed segment_forward_witness_exists))))))))
  have hall : Context Γ (allCode 7 (imp A E)) := Context.generalize 7 hv hpoint
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

theorem segment_forward_all_certificate : theoremCode (certificate segment_forward_all) =
    imp (transitiveCode 0 11 12) (imp (transitiveCode 1 16 18)
      (imp (member 0 2) (imp (member 1 5)
        (imp orderFormula.encode (imp filter (imp (graphFormula 6 2 5).encode
          (imp bijectionFormula.encode (allCode 7 (imp (member 2 7)
            (existsCode 3 restrictedWitness.encode)))))))))) :=
  certificate_correct segment_forward_all

end PASoundness.PAtoCompactSegmentForwardAll

#print axioms PASoundness.PAtoCompactSegmentForwardAll.segment_forward_all
#print axioms PASoundness.PAtoCompactSegmentForwardAll.segment_forward_all_certificate
