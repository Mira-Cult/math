import PASoundness.PAtoCompactCandidatePredecessorCore
import PASoundness.PAtoCompactQuantifiedRefutation

/-! A finite K proof constructor for the candidate-restricted induction step.
The explicit pointwise input is where the guarded PA step, successor graphs,
and capture-safe substitution still need to be aligned. No such alignment,
PA induction axiom, or semantic soundness is proved here. The endpoint
freshness forbids reuse of the successor name as a candidate binder, so
alpha transport is needed for the existing induction engine's exact syntax. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateStepGeneralization
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidatePredecessorCore
open PASoundness.PAtoCompactUniformStep PASoundness.PAtoCompactQuantifiedRefutation
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Under an explicit candidate-endpoint pointwise step and explicit K vacuity
proofs for the context, derive a candidate-restricted global step. The
context code H can contain the translated PA step and its parameter guards;
their alignment to the displayed pointwise implication is an input. -/
def candidate_restricted_step
    (Y y z w b p q v a k l h g r s d e i u j n c o t : Nat)
    (f : Formula) (H : Nat)
    (freshMember : [Y,y,b,p,q,v,a,k,l,h,g,r,s].Nodup)
    (freshSucc : [y,z,w,v,p,q,d,e,i,r,k,h,g,u,l,j,n,c,o].Nodup)
    (hvHy : KDerivation (imp H (allCode y H)))
    (hvHz : KDerivation (imp H (allCode z H)))
    (hvHY : KDerivation (imp H (allCode Y H)))
    (hvCy : KDerivation (imp (candidateCode Y b p q a k l h g)
      (allCode y (candidateCode Y b p q a k l h g))))
    (hvCz : KDerivation (imp (candidateCode Y b p q a k l h g)
      (allCode z (candidateCode Y b p q a k l h g))))
    (hpoint : KDerivation (imp H
      (imp (candidateCode y v p q r k l h g)
        (imp (candidateCode z d p q u k c h g)
          (imp (predecessorCore Y y z w p q)
            (imp (replace t y f).encode (replace t z f).encode)))))) :
    KDerivation (imp H (allCode Y
      (imp (candidateCode Y b p q a k l h g) (allStepsCode Y t y z w p q f)))) := by
  let C := candidateCode Y b p q a k l h g
  let P := predecessorCore Y y z w p q
  let Cy := candidateCode y v p q r k l h g
  let Cz := candidateCode z d p q u k c h g
  let fy := (replace t y f).encode
  let fz := (replace t z f).encode
  have hp : KDerivation (imp C (imp P (both Cy Cz))) :=
    predecessor_core_candidates Y y z w b p q v a k l h g r s d e i u j n c o freshMember freshSucc
  have hlocal : Context [C,H] (imp P (imp fy fz)) := by
    apply Context.deduction
    let Γ := [P,C,H]
    have hc : Context Γ C := .hypothesis (by simp [Γ])
    have hh : Context Γ H := .hypothesis (by simp [Γ])
    have hP : Context Γ P := .hypothesis (by simp [Γ])
    have hend : Context Γ (both Cy Cz) := .mp hP (.mp hc (.closed hp))
    have hy : Context Γ Cy := Context.conjunctionLeft hend
    have hz : Context Γ Cz := Context.conjunctionRight hend
    exact .mp hP (.mp hz (.mp hy (.mp hh (.closed hpoint))))
  have hctxY : ∀ a, a ∈ [C,H] → KDerivation (imp a (allCode y a)) := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    by_cases he : a = C
    · subst a; exact hvCy
    · have : a = H := ha.resolve_left he
      subst a; exact hvHy
  have hctxZ : ∀ a, a ∈ [C,H] → KDerivation (imp a (allCode z a)) := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    by_cases he : a = C
    · subst a; exact hvCz
    · have : a = H := ha.resolve_left he
      subst a; exact hvHz
  have hsteps : Context [C,H] (allStepsCode Y t y z w p q f) :=
    Context.generalize z hctxZ (Context.generalize y hctxY hlocal)
  have himp : Context [H] (imp C (allStepsCode Y t y z w p q f)) :=
    Context.deduction hsteps
  have hall := Context.generalize Y (Γ := [H]) (by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst a
    exact hvHY) himp
  apply Context.closeEmpty
  apply Context.deduction
  exact hall

theorem candidate_restricted_step_certificate
    (Y y z w b p q v a k l h g r s d e i u j n c o t : Nat)
    (f : Formula) (H : Nat)
    (freshMember : [Y,y,b,p,q,v,a,k,l,h,g,r,s].Nodup)
    (freshSucc : [y,z,w,v,p,q,d,e,i,r,k,h,g,u,l,j,n,c,o].Nodup)
    (hvHy : KDerivation (imp H (allCode y H)))
    (hvHz : KDerivation (imp H (allCode z H)))
    (hvHY : KDerivation (imp H (allCode Y H)))
    (hvCy : KDerivation (imp (candidateCode Y b p q a k l h g)
      (allCode y (candidateCode Y b p q a k l h g))))
    (hvCz : KDerivation (imp (candidateCode Y b p q a k l h g)
      (allCode z (candidateCode Y b p q a k l h g))))
    (hpoint : KDerivation (imp H
      (imp (candidateCode y v p q r k l h g)
        (imp (candidateCode z d p q u k c h g)
          (imp (predecessorCore Y y z w p q)
            (imp (replace t y f).encode (replace t z f).encode)))))) :
    theoremCode (certificate (candidate_restricted_step
      Y y z w b p q v a k l h g r s d e i u j n c o t f H
      freshMember freshSucc hvHy hvHz hvHY hvCy hvCz hpoint)) =
      imp H (allCode Y (imp (candidateCode Y b p q a k l h g)
        (allStepsCode Y t y z w p q f))) :=
  certificate_correct (candidate_restricted_step
    Y y z w b p q v a k l h g r s d e i u j n c o t f H
    freshMember freshSucc hvHy hvHz hvHY hvCy hvCz hpoint)

end PASoundness.PAtoCompactCandidateStepGeneralization

#print axioms PASoundness.PAtoCompactCandidateStepGeneralization.candidate_restricted_step
#print axioms PASoundness.PAtoCompactCandidateStepGeneralization.candidate_restricted_step_certificate
