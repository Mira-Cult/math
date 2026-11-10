import PASoundness.PAtoCompactRawSuccBridge
import PASoundness.PAtoCompactAdditionSuccessorCut

/-! Candidate-domain input supplies the transitivity needed to advance an
addition cut to a separately named raw result successor. No transitivity of
the relative suffix is assumed, and addition totality is not asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionCandidateCutStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactRawSuccBridge
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactAdditionSuccessorCut
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def cutAlt : Formula := namedEither (.equal 33 32) (.member 32 33)
private def cutStep : Formula := .imp (namedSuccessor 32 38 39)
  (.imp cutAlt (.member 38 33))
private def cut_step_source : KDerivation cutStep.encode := by
  simpa [cutStep,cutAlt,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,
    successorCode,Formula.encode,CompactProof.both,CompactProof.neg,CompactDerivations.either]
    using cut_in_result_successor

/-- The original cut belongs to the separately labelled successor result 45. -/
def cut_in_successor45 : KDerivation
    (imp (successorCode 32 45 39)
      (imp (either (equal 33 32) (member 32 33)) (member 45 33))) := by
  have hi := universalInstance 38 45 cutStep (by decide) (by decide) (by decide)
  have h := KDerivation.mp (.generalize 38 cut_step_source) hi
  have hs : replace 38 45 cutStep = .imp (namedSuccessor 32 45 39)
    (.imp cutAlt (.member 45 33)) := by decide
  rw [hs] at h
  simpa [cutAlt,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,
    successorCode,Formula.encode,CompactProof.both,CompactProof.neg,CompactDerivations.either]
    using h

/-- From the candidate old result, the cut alternative, and its supplied
raw successor, derive both old-result nonmembership in the cut and cut
membership in the new result. -/
def candidate_cut_step : KDerivation
    (imp (domainAt 100 32).encode
      (imp (either (equal 33 32) (member 32 33))
        (imp (successorCode 32 45 39)
          (both (neg (member 33 32)) (member 45 33))))) := by
  have ht := candidate_transitive_frame 100 38 32 (by decide) (by decide) (by decide)
  have ht' : KDerivation (imp (domainAt 100 32).encode (transitiveCode 32 42 43)) := by
    simpa [namedTransitive,transitiveBody,transitiveCode,Formula.encode] using ht
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [successorCode 32 45 39,either (equal 33 32) (member 32 33),(domainAt 100 32).encode]
  have hs : Context Γ (successorCode 32 45 39) := .head _ _
  have hc : Context Γ (either (equal 33 32) (member 32 33)) := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt 100 32).encode := .hypothesis (by simp [Γ])
  have hn : Context Γ (neg (member 33 32)) :=
    .mp hc (.mp (.mp hd (.closed ht')) (.closed result_outside_cut))
  have hm : Context Γ (member 45 33) := .mp hc (.mp hs (.closed cut_in_successor45))
  exact Context.conjunctionIntro hn hm

theorem candidate_cut_step_certificate : theoremCode (certificate candidate_cut_step) =
    imp (domainAt 100 32).encode
      (imp (either (equal 33 32) (member 32 33))
        (imp (successorCode 32 45 39)
          (both (neg (member 33 32)) (member 45 33)))) := certificate_correct candidate_cut_step
end PASoundness.PAtoCompactAdditionCandidateCutStep
#print axioms PASoundness.PAtoCompactAdditionCandidateCutStep.cut_in_successor45
#print axioms PASoundness.PAtoCompactAdditionCandidateCutStep.candidate_cut_step
#print axioms PASoundness.PAtoCompactAdditionCandidateCutStep.candidate_cut_step_certificate
