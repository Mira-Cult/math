import PASoundness.PAtoCompactInductionConcludeGeneralize
import PASoundness.PAtoCompactInductionConclusionBody
import PASoundness.PAtoCompactDomainCandidateReverse

/-! Constructive K packaging of a pointwise candidate induction conclusion
into the literal guarded PA induction axiom. The pointwise implication remains
an explicit finite K proof input; base, step and name allocation are not
claimed here. -/
namespace PASoundness.PAtoCompactInductionConclusionAligned
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactDirectGeneralization PASoundness.PAtoCompactGuardedAllImpAlignment
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactDomainCandidateReverse
open PASoundness.PAtoCompactInductionConclusionBody PASoundness.PAtoCompactInductionConcludeGeneralize

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Under explicit source and binder freshness, a finite K pointwise proof
with the actual candidate and named induction predicate closes to the literal
guarded PA induction axiom. The pointwise proof is genuine K proof data. -/
noncomputable def close_from_candidate_pointwise
    (φ : Peano.Formula) (x z b p q u t l m r : Nat)
    (hgt : topName x φ < z) (hz : z ∉ (originalChild φ x).names)
    (hfresh : z ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (htop : topName x φ < t) (hzt : z < t)
    (fresh : [z,b,p,q,u,t,l,m,r].Nodup)
    (hpoint : KDerivation (imp (guardFormula (Peano.inductionAxiom φ x)).encode
      (imp (code (FOL.substAt φ x Peano.zero))
        (imp (code (FOL.allAt x (φ.imp (FOL.substAt φ x (Peano.succ (.var x))))))
          (imp (candidateCode z b p q u t l m r)
            (replace t z (scopeAt φ x t)).encode))))) :
    KDerivation (guardedCode (Peano.inductionAxiom φ x)) := by
  have hd := domain_to_candidate z b p q u t l m r (z+1) fresh (by omega)
  have hb := (conclusion_body_alignment φ x t z htop hzt).1
  exact close_pa_induction_conclusion φ x z _ _ hgt hz hfresh hpoint hd hb

theorem close_from_candidate_pointwise_certificate
    (φ : Peano.Formula) (x z b p q u t l m r : Nat)
    (hgt : topName x φ < z) (hz : z ∉ (originalChild φ x).names)
    (hfresh : z ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (htop : topName x φ < t) (hzt : z < t)
    (fresh : [z,b,p,q,u,t,l,m,r].Nodup)
    (hpoint : KDerivation (imp (guardFormula (Peano.inductionAxiom φ x)).encode
      (imp (code (FOL.substAt φ x Peano.zero))
        (imp (code (FOL.allAt x (φ.imp (FOL.substAt φ x (Peano.succ (.var x))))))
          (imp (candidateCode z b p q u t l m r)
            (replace t z (scopeAt φ x t)).encode))))) :
    theoremCode (certificate (close_from_candidate_pointwise φ x z b p q u t l m r
      hgt hz hfresh htop hzt fresh hpoint)) = guardedCode (Peano.inductionAxiom φ x) :=
  certificate_correct _

end PASoundness.PAtoCompactInductionConclusionAligned

#print axioms PASoundness.PAtoCompactInductionConclusionAligned.close_from_candidate_pointwise
#print axioms PASoundness.PAtoCompactInductionConclusionAligned.close_from_candidate_pointwise_certificate
