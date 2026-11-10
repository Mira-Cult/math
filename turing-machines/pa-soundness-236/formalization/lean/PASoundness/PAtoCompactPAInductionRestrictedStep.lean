import PASoundness.PAtoCompactPAInductionPointwise
import PASoundness.PAtoCompactInductionStepQuantifierAssembly
import PASoundness.PAtoCompactInductionSubstitutionSyntax

/-! Conditional derivation of the candidate-restricted K step from the actual
translated PA induction step. The variable instantiation and predecessor
endpoint construction are proved; domain, predicate and successor alignment
and the displayed K vacuity proofs remain explicit inputs. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAInductionRestrictedStep

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllElim
open PASoundness.PAtoCompactPAInductionPointwise PASoundness.PAtoCompactInductionStepQuantifierAssembly
open PASoundness.PAtoCompactInductionSubstitutionSyntax PASoundness.PAtoCompactQuantifiedRefutation

/-- Finite K proof that the actual PA step yields the candidate-restricted
uniform step, conditional on displayed alignment proofs and vacuity proofs. -/
noncomputable def pa_restricted_step
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
          (imp (code (FOL.substAt φ x (Peano.succ (.var y))))
            (CompactNamed.replace t z f).encode)))))
    (vacY : ∀ H, H ∈ [code (FOL.allAt x (paStep φ x)), pointGuard φ x] →
      KDerivation (imp H (allCode Y H)))
    (vacy : ∀ H, H ∈ [candidateCode Y b p q a k l h g,
        code (FOL.allAt x (paStep φ x)), pointGuard φ x] →
      KDerivation (imp H (allCode y H)))
    (vacz : ∀ H, H ∈ [candidateCode Y b p q a k l h g,
        code (FOL.allAt x (paStep φ x)), pointGuard φ x] →
      KDerivation (imp H (allCode z H))) :
    KDerivation (imp (pointGuard φ x) (imp (code (FOL.allAt x (paStep φ x)))
      (allCode Y (imp (candidateCode Y b p q a k l h g)
        (allStepsCode Y t y z w p q f))))) := by
  have hs : KDerivation (imp (pointGuard φ x)
      (imp (candidateCode z d p q u k c h g)
        (imp (predecessorCore Y y z w p q)
          (imp (code (FOL.substAt (FOL.substAt φ x (Peano.succ (.var x))) x (.var y)))
            (CompactNamed.replace t z f).encode)))) := by
    rw [subst_successor_then_variable]
    exact successorAlignment
  have hp := pa_step_pointwise φ x t f Y y z w b p q v a k l h g r s d e i u j n c o
    freshMember freshSucc domainAlignment predicateAlignment hs
  exact quantified_restricted_step (pointGuard φ x) (code (FOL.allAt x (paStep φ x)))
    (candidateCode Y b p q a k l h g) Y t y z w p q f hp vacY vacy vacz

theorem pa_restricted_step_certificate
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
          (imp (code (FOL.substAt φ x (Peano.succ (.var y))))
            (CompactNamed.replace t z f).encode)))))
    (vacY : ∀ H, H ∈ [code (FOL.allAt x (paStep φ x)), pointGuard φ x] →
      KDerivation (imp H (allCode Y H)))
    (vacy : ∀ H, H ∈ [candidateCode Y b p q a k l h g,
        code (FOL.allAt x (paStep φ x)), pointGuard φ x] →
      KDerivation (imp H (allCode y H)))
    (vacz : ∀ H, H ∈ [candidateCode Y b p q a k l h g,
        code (FOL.allAt x (paStep φ x)), pointGuard φ x] →
      KDerivation (imp H (allCode z H))) :
    theoremCode (certificate (pa_restricted_step φ x t f Y y z w b p q v a k l h g r s d e i u j n c o
      freshMember freshSucc domainAlignment predicateAlignment successorAlignment vacY vacy vacz)) =
      imp (pointGuard φ x) (imp (code (FOL.allAt x (paStep φ x)))
        (allCode Y (imp (candidateCode Y b p q a k l h g) (allStepsCode Y t y z w p q f)))) :=
  certificate_correct _

end PASoundness.PAtoCompactPAInductionRestrictedStep

#print axioms PASoundness.PAtoCompactPAInductionRestrictedStep.pa_restricted_step
#print axioms PASoundness.PAtoCompactPAInductionRestrictedStep.pa_restricted_step_certificate
