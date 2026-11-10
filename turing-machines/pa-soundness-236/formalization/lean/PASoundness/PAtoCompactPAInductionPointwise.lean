import PASoundness.PAtoCompactCandidatePredecessorCore
import PASoundness.PAtoCompactAllElimVariableFull

/-! A conditional finite-K bridge from the actual translated PA induction
step to one step of the candidate-domain induction engine. The name and graph
alignments are explicit finite-K proof inputs; this is not a PA induction proof. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAInductionPointwise

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidatePredecessorCore
open PASoundness.PAtoCompactUniformStep PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedAllElim PASoundness.PAtoCompactAllElimVariableFull

def paStep (φ : Peano.Formula) (x : Nat) : Peano.Formula :=
  φ.imp (FOL.substAt φ x (Peano.succ (.var x)))

def pointGuard (φ : Peano.Formula) (x : Nat) : Nat :=
  (guardFormula (Peano.inductionAxiom φ x)).encode

/-- Given finite K proofs aligning the induction predicate and successor
substitution with the named K predicate, the actual translated PA step implies
one local candidate-domain step. The two endpoint candidate witnesses are
constructed from the candidate container and predecessor core, not assumed as
independent premises. The three alignment derivations remain explicit. -/
noncomputable def pa_step_pointwise
    (φ : Peano.Formula) (x t : Nat) (f : CompactNamed.Formula)
    (Y y z w b p q v a k l h g r s d e i u j n c o : Nat)
    (freshMember : [Y,y,b,p,q,v,a,k,l,h,g,r,s].Nodup)
    (freshSucc : [y,z,w,v,p,q,d,e,i,r,k,h,g,u,l,j,n,c,o].Nodup)
    (domainAlignment : KDerivation (imp (candidateCode y v p q r k l h g)
      (domainAt (instanceBinder (paStep φ x) x y + 1) y).encode))
    (predicateAlignment : KDerivation (imp (pointGuard φ x)
      (imp (candidateCode y v p q r k l h g)
        (imp (CompactNamed.replace t y f).encode
          (code (FOL.substAt φ x (.var y)))))))
    (successorAlignment : KDerivation (imp (pointGuard φ x)
      (imp (candidateCode z d p q u k c h g)
        (imp (predecessorCore Y y z w p q)
          (imp (code (FOL.substAt (FOL.substAt φ x (Peano.succ (.var x))) x (.var y)))
            (CompactNamed.replace t z f).encode))))) :
    KDerivation (imp (pointGuard φ x)
      (imp (code (FOL.allAt x (paStep φ x)))
        (imp (candidateCode Y b p q a k l h g)
          (imp (predecessorCore Y y z w p q)
            (imp (CompactNamed.replace t y f).encode
              (CompactNamed.replace t z f).encode))))) := by
  let G := pointGuard φ x
  let A := code (FOL.allAt x (paStep φ x))
  let D := candidateCode Y b p q a k l h g
  let P := predecessorCore Y y z w p q
  let Fy := (CompactNamed.replace t y f).encode
  let Fz := (CompactNamed.replace t z f).encode
  let Cy := candidateCode y v p q r k l h g
  let Cz := candidateCode z d p q u k c h g
  let Φy := code (FOL.substAt φ x (.var y))
  let Ψy := code (FOL.substAt (FOL.substAt φ x (Peano.succ (.var x))) x (.var y))
  have hshape : code (FOL.substAt (paStep φ x) x (.var y)) = imp Φy Ψy := by rfl
  have hinst := variable_instance (paStep φ x) x y
  rw [hshape] at hinst
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [Fy,P,D,A,G]
  have hf : Context Γ Fy := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hend : Context Γ (both Cy Cz) :=
    .mp hp (.mp hd (.closed (predecessor_core_candidates Y y z w b p q v a k l h g r s d e i u j n c o freshMember freshSucc)))
  have hcy : Context Γ Cy := Context.conjunctionLeft hend
  have hcz : Context Γ Cz := Context.conjunctionRight hend
  have hdom := Context.mp hcy (.closed domainAlignment)
  have hstep : Context Γ (imp Φy Ψy) := .mp hdom (.mp ha (.closed hinst))
  have hphi : Context Γ Φy := .mp hf (.mp hcy (.mp hg (.closed predicateAlignment)))
  have hpsi : Context Γ Ψy := .mp hphi hstep
  exact .mp hpsi (.mp hp (.mp hcz (.mp hg (.closed successorAlignment))))

theorem pa_step_pointwise_certificate
    (φ : Peano.Formula) (x t : Nat) (f : CompactNamed.Formula)
    (Y y z w b p q v a k l h g r s d e i u j n c o : Nat)
    (freshMember : [Y,y,b,p,q,v,a,k,l,h,g,r,s].Nodup)
    (freshSucc : [y,z,w,v,p,q,d,e,i,r,k,h,g,u,l,j,n,c,o].Nodup)
    (domainAlignment : KDerivation (imp (candidateCode y v p q r k l h g)
      (domainAt (instanceBinder (paStep φ x) x y + 1) y).encode))
    (predicateAlignment : KDerivation (imp (pointGuard φ x)
      (imp (candidateCode y v p q r k l h g)
        (imp (CompactNamed.replace t y f).encode
          (code (FOL.substAt φ x (.var y)))))))
    (successorAlignment : KDerivation (imp (pointGuard φ x)
      (imp (candidateCode z d p q u k c h g)
        (imp (predecessorCore Y y z w p q)
          (imp (code (FOL.substAt (FOL.substAt φ x (Peano.succ (.var x))) x (.var y)))
            (CompactNamed.replace t z f).encode))))) :
    theoremCode (certificate (pa_step_pointwise φ x t f Y y z w b p q v a k l h g r s d e i u j n c o
      freshMember freshSucc domainAlignment predicateAlignment successorAlignment)) =
      imp (pointGuard φ x) (imp (code (FOL.allAt x (paStep φ x)))
        (imp (candidateCode Y b p q a k l h g) (imp (predecessorCore Y y z w p q)
          (imp (CompactNamed.replace t y f).encode (CompactNamed.replace t z f).encode)))) :=
  certificate_correct _

end PASoundness.PAtoCompactPAInductionPointwise

#print axioms PASoundness.PAtoCompactPAInductionPointwise.pa_step_pointwise
#print axioms PASoundness.PAtoCompactPAInductionPointwise.pa_step_pointwise_certificate
