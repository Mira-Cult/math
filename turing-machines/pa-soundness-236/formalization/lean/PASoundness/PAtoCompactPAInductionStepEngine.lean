import PASoundness.PAtoCompactPAInductionRestrictedStep
import PASoundness.PAtoCompactCandidateStepBinderTransport
import PASoundness.PAtoCompactInductionStepContextVacuity
import PASoundness.PAtoCompactCandidateWitness

/-! Finite-K assembly of the actual PA induction step into the literal
candidate-restricted induction engine's step interface. Domain, predicate and
successor alignments remain explicit K proof inputs. No PA induction axiom is
proved here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAInductionStepEngine

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllElim
open PASoundness.PAtoCompactPAInductionPointwise PASoundness.PAtoCompactPAInductionRestrictedStep
open PASoundness.PAtoCompactInductionStepContextVacuity PASoundness.PAtoCompactGuardedVacuity
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactCandidateWitness
open PASoundness.PAtoCompactCandidateStepBinderTransport PASoundness.PAtoCompactQuantifiedRefutation

/-- The exact displayed candidate binder matches `candidate_restricted_induction`.
Vacuity proofs are constructed from source free-name freshness and pairwise
candidate-name freshness. The remaining alignment inputs are finite K proofs. -/
noncomputable def pa_step_engine
    (φ : Peano.Formula) (x t : Nat) (f : CompactNamed.Formula)
    (Y y z w b p q v a k l h g r s d e i u j n c o : Nat)
    (freshMember : [Y,y,b,p,q,v,a,k,l,h,g,r,s].Nodup)
    (freshSucc : [y,z,w,v,p,q,d,e,i,r,k,h,g,u,l,j,n,c,o].Nodup)
    (freshCy : [Y,b,p,q,a,k,l,h,g,y].Nodup)
    (freshCz : [Y,b,p,q,a,k,l,h,g,z].Nodup)
    (freshG : [Y,a,k,z,g,h].Nodup)
    (freshL : [Y,a,k,l,z,g,h].Nodup)
    (freshY : Y ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (freshy : y ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (freshz : z ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (domainAlignment : KDerivation (imp (candidateCode y v p q r k l h g)
      (domainAt (instanceBinder (PAtoCompactPAInductionPointwise.paStep φ x) x y + 1) y).encode))
    (predicateAlignment : KDerivation (imp (pointGuard φ x)
      (imp (candidateCode y v p q r k l h g)
        (imp (CompactNamed.replace t y f).encode
          (code (FOL.substAt φ x (.var y)))))))
    (successorAlignment : KDerivation (imp (pointGuard φ x)
      (imp (candidateCode z d p q u k c h g)
        (imp (predecessorCore Y y z w p q)
          (imp (code (FOL.substAt φ x (Peano.succ (.var y))))
            (CompactNamed.replace t z f).encode))))) :
    KDerivation (imp (pointGuard φ x)
      (imp (code (FOL.allAt x (PAtoCompactPAInductionPointwise.paStep φ x)))
        (allCode Y (imp (candidateCode Y b p q a k l z g)
          (allStepsCode Y t y z w p q f))))) := by
  let G := pointGuard φ x
  let A := code (FOL.allAt x (PAtoCompactPAInductionPointwise.paStep φ x))
  let C := candidateCode Y b p q a k l h g
  have vG (N : Nat) (hN : N ∉ (Peano.inductionAxiom φ x).freeVarFinset) :
      KDerivation (imp G (allCode N G)) :=
    guardFormula_vacuity (Peano.inductionAxiom φ x) N hN
  have vA (N : Nat) (hN : N ∉ (Peano.inductionAxiom φ x).freeVarFinset) :
      KDerivation (imp A (allCode N A)) := by
    apply translated_vacuity
    intro h
    exact hN (paStep_free_subset φ x h)
  have vY : ∀ H, H ∈ [A,G] → KDerivation (imp H (allCode Y H)) := by
    intro H hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : H = A
    · subst H; exact vA Y freshY
    · have he' : H = G := hh.resolve_left he
      subst H; exact vG Y freshY
  have vy : ∀ H, H ∈ [C,A,G] → KDerivation (imp H (allCode y H)) := by
    intro H hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : H = C
    · subst H; exact candidate_vacuity Y b p q a k l h g y freshCy
    · have hr := hh.resolve_left he
      by_cases he' : H = A
      · subst H; exact vA y freshy
      · have he'' : H = G := hr.resolve_left he'
        subst H; exact vG y freshy
  have vz : ∀ H, H ∈ [C,A,G] → KDerivation (imp H (allCode z H)) := by
    intro H hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : H = C
    · subst H; exact candidate_vacuity Y b p q a k l h g z freshCz
    · have hr := hh.resolve_left he
      by_cases he' : H = A
      · subst H; exact vA z freshz
      · have he'' : H = G := hr.resolve_left he'
        subst H; exact vG z freshz
  have hstep := pa_restricted_step φ x t f Y y z w b p q v a k l h g r s d e i u j n c o
    freshMember freshSucc domainAlignment predicateAlignment successorAlignment vY vy vz
  have halign := restricted_step_witness_transport Y b p q a k l z g h t y w f freshG freshL
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [A,G]
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  exact .mp (.mp ha (.mp hg (.closed hstep))) (.closed halign)

theorem pa_step_engine_certificate
    (φ : Peano.Formula) (x t : Nat) (f : CompactNamed.Formula)
    (Y y z w b p q v a k l h g r s d e i u j n c o : Nat)
    (freshMember : [Y,y,b,p,q,v,a,k,l,h,g,r,s].Nodup)
    (freshSucc : [y,z,w,v,p,q,d,e,i,r,k,h,g,u,l,j,n,c,o].Nodup)
    (freshCy : [Y,b,p,q,a,k,l,h,g,y].Nodup)
    (freshCz : [Y,b,p,q,a,k,l,h,g,z].Nodup)
    (freshG : [Y,a,k,z,g,h].Nodup)
    (freshL : [Y,a,k,l,z,g,h].Nodup)
    (freshY : Y ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (freshy : y ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (freshz : z ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (domainAlignment : KDerivation (imp (candidateCode y v p q r k l h g)
      (domainAt (instanceBinder (PAtoCompactPAInductionPointwise.paStep φ x) x y + 1) y).encode))
    (predicateAlignment : KDerivation (imp (pointGuard φ x)
      (imp (candidateCode y v p q r k l h g)
        (imp (CompactNamed.replace t y f).encode
          (code (FOL.substAt φ x (.var y)))))))
    (successorAlignment : KDerivation (imp (pointGuard φ x)
      (imp (candidateCode z d p q u k c h g)
        (imp (predecessorCore Y y z w p q)
          (imp (code (FOL.substAt φ x (Peano.succ (.var y))))
            (CompactNamed.replace t z f).encode))))) :
    theoremCode (certificate (pa_step_engine φ x t f Y y z w b p q v a k l h g r s d e i u j n c o
      freshMember freshSucc freshCy freshCz freshG freshL freshY freshy freshz
      domainAlignment predicateAlignment successorAlignment)) =
      imp (pointGuard φ x)
        (imp (code (FOL.allAt x (PAtoCompactPAInductionPointwise.paStep φ x)))
          (allCode Y (imp (candidateCode Y b p q a k l z g)
            (allStepsCode Y t y z w p q f)))) :=
  certificate_correct _

end PASoundness.PAtoCompactPAInductionStepEngine

#print axioms PASoundness.PAtoCompactPAInductionStepEngine.pa_step_engine
#print axioms PASoundness.PAtoCompactPAInductionStepEngine.pa_step_engine_certificate
