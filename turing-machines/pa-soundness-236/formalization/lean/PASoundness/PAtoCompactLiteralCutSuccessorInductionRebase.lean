import PASoundness.PAtoCompactAdditionLiteralCutStepSpecialize
import PASoundness.PAtoCompactAdditionInductionPointClosed

/-! Capture-safe rebase of the literal-cut successor law to the names used by
candidate induction. Candidate and successor conditions remain object-level
antecedents; this is not an induction or totality theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutSuccessorInductionRebase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactRawSuccBridge PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactLiteralCutAdditionDefinition
open PASoundness.PAtoCompactAdditionSuccessorLocalStep
open PASoundness.PAtoCompactAdditionLiteralCutStepSpecialize
open PASoundness.PAtoCompactAdditionInductionPointClosed
attribute [local irreducible] imp Cantor.pair Cantor.triangle

def original : Formula := .imp fixedAssumptions (.imp literalCut literalCut45)
def inductionInstance : Formula := replace 38 205 (replace 31 204 original)

/-- Reindexing retains both candidate guards and the two distinct successors. -/
theorem induction_instance_shape : inductionInstance =
    .imp (namedBoth (domainAt 100 204) (namedBoth (domainAt 100 32)
      (namedBoth (namedSuccessor 204 205 39) (namedSuccessor 32 45 39))))
      (.imp (replace 31 204 literalCut)
        (replace 32 45 (replace 31 205 literalCut))) := by decide

/-- The actual finite K successor derivation at the induction names. -/
def successor_at_induction : KDerivation inductionInstance.encode := by
  have h : KDerivation original.encode := literal_cut_successor
  have h1 : KDerivation (replace 31 204 original).encode :=
    .mp (.generalize 31 h) (universalInstance 31 204 original (by decide) (by decide) (by decide))
  exact .mp (.generalize 38 h1)
    (universalInstance 38 205 (replace 31 204 original) (by decide) (by decide) (by decide))

/-- Curried exact local successor law with the test binder used by the
candidate-induction predecessor relation. -/
def local_successor : KDerivation (imp (domainAt 100 204).encode
    (imp (domainAt 100 32).encode
      (imp (successorCode 204 205 208) (imp (successorCode 32 45 39)
        (imp (replace 31 204 literalCut).encode
          (replace 32 45 (replace 31 205 literalCut)).encode))))) := by
  have h : KDerivation (imp
      (both (domainAt 100 204).encode (both (domainAt 100 32).encode
        (both (successorCode 204 205 39) (successorCode 32 45 39))))
      (imp (replace 31 204 literalCut).encode
        (replace 32 45 (replace 31 205 literalCut)).encode)) := by
    have h := successor_at_induction
    rw [induction_instance_shape] at h
    change KDerivation (imp
      (both (domainAt 100 204).encode (both (domainAt 100 32).encode
        (both (successorCode 204 205 39) (successorCode 32 45 39))))
      (imp (replace 31 204 literalCut).encode
        (replace 32 45 (replace 31 205 literalCut)).encode)) at h
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
  let A := (replace 31 204 literalCut).encode
  let Γ := [A,T,S,E,D]
  have ha : Context Γ A := .head _ _
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hs' : Context Γ (successorCode 204 205 39) := .mp hs (.closed successor_test_alpha)
  have hp := Context.conjunctionIntro hd (Context.conjunctionIntro he (Context.conjunctionIntro hs' ht))
  exact .mp ha (.mp hp (.closed h))

theorem local_successor_certificate : theoremCode (certificate local_successor) =
    imp (domainAt 100 204).encode (imp (domainAt 100 32).encode
      (imp (successorCode 204 205 208) (imp (successorCode 32 45 39)
        (imp (replace 31 204 literalCut).encode
          (replace 32 45 (replace 31 205 literalCut)).encode)))) :=
  certificate_correct local_successor
end PASoundness.PAtoCompactLiteralCutSuccessorInductionRebase
#print axioms PASoundness.PAtoCompactLiteralCutSuccessorInductionRebase.successor_at_induction
#print axioms PASoundness.PAtoCompactLiteralCutSuccessorInductionRebase.local_successor
#print axioms PASoundness.PAtoCompactLiteralCutSuccessorInductionRebase.local_successor_certificate
