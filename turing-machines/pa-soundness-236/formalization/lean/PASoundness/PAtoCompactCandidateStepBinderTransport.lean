import PASoundness.PAtoCompactCandidateFieldTransport
import PASoundness.PAtoCompactQuantifiedRefutation

/-! Finite K alpha transport for the candidate antecedent in the restricted
induction step. This connects a fresh witness binder to the literal induction
engine's reuse of the step's quantified endpoint label. No step schema or PA
induction axiom is asserted here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateStepBinderTransport
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateFieldTransport
open PASoundness.PAtoCompactQuantifiedRefutation
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Rebase the global-step candidate antecedent from the fresh witness binder
h to the engine's bound endpoint label z. Other candidate binders and the
entire step body remain unchanged. -/
def restricted_step_witness_transport
    (Y b p q a k l z g h t y w : Nat) (f : Formula)
    (freshG : [Y,a,k,z,g,h].Nodup)
    (freshL : [Y,a,k,l,z,g,h].Nodup) :
    KDerivation (imp
      (allCode Y (imp (candidateCode Y b p q a k l h g)
        (allStepsCode Y t y z w p q f)))
      (allCode Y (imp (candidateCode Y b p q a k l z g)
        (allStepsCode Y t y z w p q f)))) := by
  let C := candidateCode Y b p q a k l z g
  let C' := candidateCode Y b p q a k l h g
  let L := allStepsCode Y t y z w p q f
  have hc : KDerivation (imp C C') := witness_field Y b p q a k l z g h freshG freshL
  have hp : KDerivation (imp (imp C' L) (imp C L)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [C, imp C' L]
    have hC : Context Γ C := .hypothesis (by simp [Γ])
    have hi : Context Γ (imp C' L) := .hypothesis (by simp [Γ])
    exact .mp (.mp hC (.closed hc)) hi
  exact allCongr Y hp

theorem restricted_step_witness_transport_certificate
    (Y b p q a k l z g h t y w : Nat) (f : Formula)
    (freshG : [Y,a,k,z,g,h].Nodup)
    (freshL : [Y,a,k,l,z,g,h].Nodup) :
    theoremCode (certificate (restricted_step_witness_transport
      Y b p q a k l z g h t y w f freshG freshL)) =
      imp (allCode Y (imp (candidateCode Y b p q a k l h g)
        (allStepsCode Y t y z w p q f)))
        (allCode Y (imp (candidateCode Y b p q a k l z g)
          (allStepsCode Y t y z w p q f))) :=
  certificate_correct (restricted_step_witness_transport
    Y b p q a k l z g h t y w f freshG freshL)

end PASoundness.PAtoCompactCandidateStepBinderTransport

#print axioms PASoundness.PAtoCompactCandidateStepBinderTransport.restricted_step_witness_transport
#print axioms PASoundness.PAtoCompactCandidateStepBinderTransport.restricted_step_witness_transport_certificate
