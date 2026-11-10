import PASoundness.PAtoCompactSegmentForwardUnique
import PASoundness.PAtoCompactSegmentForwardOrder
import PASoundness.PAtoCompactTransitiveWitness
import PASoundness.PAtoCompactBijectionVacuity
import PASoundness.PAtoCompactOrderIsoVacuity

/-! One forward initial-segment witness from an explicit isomorphism edge and
supplied endpoint filter. Both outer transitivity, endpoint membership and
all graph clauses are explicit K hypotheses; no semantics is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentForwardExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactBijectionForwardAtSeven PASoundness.PAtoCompactBijectionVacuity
open PASoundness.PAtoCompactOrderIsoVacuity PASoundness.PAtoCompactRestrictionFilterVacuity
open PASoundness.PAtoCompactRestrictedForwardPoint PASoundness.PAtoCompactRestrictedForwardUnique
open PASoundness.PAtoCompactSegmentForwardUnique PASoundness.PAtoCompactSegmentForwardOrder
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A member of the source initial segment has a unique image in the target
initial segment, represented in the supplied filtered graph. -/
def segment_forward_witness_exists : KDerivation
    (imp (transitiveCode 0 11 12) (imp (transitiveCode 1 16 18)
      (imp (member 0 2) (imp (member 1 5)
        (imp orderFormula.encode (imp filter (imp (graphFormula 6 2 5).encode
          (imp bijectionFormula.encode (imp (member 2 7)
            (existsCode 3 restrictedWitness.encode)))))))))) := by
  let T0 := transitiveCode 0 11 12
  let T1 := transitiveCode 1 16 18
  let M0 := member 0 2
  let M1 := member 1 5
  let O := orderFormula.encode
  let F := filter
  let Top := (graphFormula 6 2 5).encode
  let B := bijectionFormula.encode
  let L := member 2 7
  let W := witnessAtSeven.encode
  let H := restrictedWitness.encode
  let Γ := [L,B,Top,F,O,M1,M0,T1,T0]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 3 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = L
    · subst z; exact membershipVacuity 2 7 3 (by decide) (by decide)
    by_cases he : z = B
    · subst z; exact bijection_vacuity_three
    by_cases he : z = Top
    · subst z; exact (graphFormula 6 2 5).vacuity 3 (by decide)
    by_cases he : z = F
    · subst z
      simpa only [F, filter] using (restriction_filter_vacuity 6 8 14 2 5 3 (by decide))
    by_cases he : z = O
    · subst z; exact order_vacuity 3 order_fresh_3
    by_cases he : z = M1
    · subst z; exact membershipVacuity 1 5 3 (by decide) (by decide)
    by_cases he : z = M0
    · subst z; exact membershipVacuity 0 2 3 (by decide) (by decide)
    by_cases he : z = T1
    · subst z; exact transitive_vacuity 1 16 18 3 (by decide) (by decide) (by decide)
    have he : z = T0 := by simp_all
    subst z
    exact transitive_vacuity 0 11 12 3 (by decide) (by decide) (by decide)
  have hlocal : Context Γ (imp W H) := by
    apply Context.deduction
    let Δ := W :: Γ
    have hw : Context Δ W := .head _ _
    have hm : Context Δ (member 1 3) := Context.conjunctionLeft hw
    have hg : Context Δ (graphFormula 6 7 3).encode := Context.conjunctionLeft (Context.conjunctionRight hw)
    have ht0 : Context Δ T0 := .hypothesis (by simp [Δ,Γ])
    have ht1 : Context Δ T1 := .hypothesis (by simp [Δ,Γ])
    have h0 : Context Δ M0 := .hypothesis (by simp [Δ,Γ])
    have h1 : Context Δ M1 := .hypothesis (by simp [Δ,Γ])
    have ho : Context Δ O := .hypothesis (by simp [Δ,Γ])
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have htop : Context Δ Top := .hypothesis (by simp [Δ,Γ])
    have hl : Context Δ L := .hypothesis (by simp [Δ,Γ])
    have hy : Context Δ (member 5 3) := .mp ho (.mp htop (.mp hg (.mp h1
      (.mp hm (.mp hl (.mp h0 (.mp ht0 (.closed forward_segment_order))))))))
    have hnew : Context Δ (graphFormula 8 7 3).encode :=
      .mp hg (.mp hy (.mp hl (.mp hf (.closed retain_old_point))))
    have hr := Context.conjunctionIntro hy hnew
    exact .mp hr (.mp hw (.mp hf (.mp h1 (.mp ht1 (.closed segment_witness_from_original)))))
  have hex : Context Γ (existsCode 3 W) := by
    have ht : Context Γ T0 := .hypothesis (by simp [Γ])
    have h0 : Context Γ M0 := .hypothesis (by simp [Γ])
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have hl : Context Γ L := .head _ _
    have hi : Context Γ (member 0 7) := .mp hl (.mp h0 (.mp ht (.closed
      (transitive_chain 0 11 12 2 7 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)))))
    exact .mp hi (.mp hb (.closed forward_witness_at_seven))
  have hresult : Context Γ (existsCode 3 H) :=
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
  exact hresult

theorem segment_forward_witness_certificate : theoremCode (certificate segment_forward_witness_exists) =
    imp (transitiveCode 0 11 12) (imp (transitiveCode 1 16 18)
      (imp (member 0 2) (imp (member 1 5)
        (imp orderFormula.encode (imp filter (imp (graphFormula 6 2 5).encode
          (imp bijectionFormula.encode (imp (member 2 7)
            (existsCode 3 restrictedWitness.encode))))))))) :=
  certificate_correct segment_forward_witness_exists

end PASoundness.PAtoCompactSegmentForwardExists

#print axioms PASoundness.PAtoCompactSegmentForwardExists.segment_forward_witness_exists
