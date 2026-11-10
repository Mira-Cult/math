import PASoundness.PAtoCompactAdditionInductionPointStep
import PASoundness.PAtoCompactAdditionSuccessorInductionRebase
import PASoundness.PAtoCompactRawSuccBridge

/-! Closes the candidate-guarded addition point step using the actual
addition-successor proof. The candidate and predecessor core remain literal
K antecedents; the successor-name test is alpha-converted from 208 to 39.
This module alone is not an induction or addition-totality theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionInductionPointClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactRawSuccBridge PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactAdditionCandidateInductionInstance
open PASoundness.PAtoCompactAdditionInductionWitnessBind
open PASoundness.PAtoCompactAdditionInductionPointStep
open PASoundness.PAtoCompactAdditionSuccessorInductionRebase
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Convert only the test binder in the predecessor successor graph. -/
def successor_test_alpha : KDerivation (imp (successorCode 204 205 208)
    (successorCode 204 205 39)) := by
  have h := raw_successor_alpha 204 205 208 39 (by decide) (by decide)
    (by decide) (by decide) (by decide)
  simpa [namedSuccessor,namedSuccessorBody,namedBoth,namedEither,successorCode,
    Formula.encode,CompactProof.both,CompactProof.neg,CompactDerivations.either] using h

/-- The actual finite K successor step, with curried assumptions and the test
binder required by the candidate induction engine. -/
def local_successor : KDerivation (imp (domainAt 100 204).encode
    (imp (domainAt 100 32).encode
      (imp (successorCode 204 205 208) (imp (successorCode 32 45 39)
        (imp oldAdd.encode newAdd.encode))))) := by
  have h : KDerivation (imp
      (both (domainAt 100 204).encode (both (domainAt 100 32).encode
        (both (successorCode 204 205 39) (successorCode 32 45 39))))
      (imp oldAdd.encode newAdd.encode)) := by
    have h := successor_step_at_induction
    rw [induction_instance_shape] at h
    change KDerivation (imp
      (both (domainAt 100 204).encode (both (domainAt 100 32).encode
        (both (successorCode 204 205 39) (successorCode 32 45 39))))
      (imp oldAdd.encode newAdd.encode)) at h
    exact h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let D := (domainAt 100 204).encode
  let E := (domainAt 100 32).encode
  let S := successorCode 204 205 208
  let T := successorCode 32 45 39
  let A := oldAdd.encode
  let Γ := [A,T,S,E,D]
  have ha : Context Γ A := .head _ _
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hs' : Context Γ (successorCode 204 205 39) := .mp hs (.closed successor_test_alpha)
  have hp := Context.conjunctionIntro hd (Context.conjunctionIntro he (Context.conjunctionIntro hs' ht))
  exact .mp ha (.mp hp (.closed h))

/-- The actual point-step certificate for the restricted induction engine;
the successor candidate is an additional antecedent which this point proof
does not need. -/
def point_closed : KDerivation
    (imp (candidateCode 204 230 209 210 232 31 203 231 206)
      (imp (candidateCode 205 234 209 210 237 31 240 231 206)
        (imp (predecessorCore 201 204 205 208 209 210)
          (imp (replace 31 204 predicate).encode (replace 31 205 predicate).encode)))) := by
  let C := candidateCode 204 230 209 210 232 31 203 231 206
  let D := candidateCode 205 234 209 210 237 31 240 231 206
  let P := predecessorCore 201 204 205 208 209 210
  let F := (replace 31 204 predicate).encode
  let Γ := [F,P,D,C]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hf : Context Γ F := .head _ _
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  exact .mp hf (.mp hp (.mp hc (.closed (guarded_point local_successor))))

theorem point_closed_certificate : theoremCode (certificate point_closed) =
    imp (candidateCode 204 230 209 210 232 31 203 231 206)
      (imp (candidateCode 205 234 209 210 237 31 240 231 206)
        (imp (predecessorCore 201 204 205 208 209 210)
          (imp (replace 31 204 predicate).encode (replace 31 205 predicate).encode))) :=
  certificate_correct point_closed
end PASoundness.PAtoCompactAdditionInductionPointClosed
#print axioms PASoundness.PAtoCompactAdditionInductionPointClosed.successor_test_alpha
#print axioms PASoundness.PAtoCompactAdditionInductionPointClosed.local_successor
#print axioms PASoundness.PAtoCompactAdditionInductionPointClosed.point_closed
#print axioms PASoundness.PAtoCompactAdditionInductionPointClosed.point_closed_certificate
