import PASoundness.PAtoCompactFixedFirstLocalSuccessorClosed
import PASoundness.PAtoCompactRawSuccessorBinderBridge

/-! Capture-safe reindexing of the closed fixed-first row successor proof to
names used by candidate induction. The map bijection remains an object-level
hypothesis. This is a local step, not yet row collection or multiplication. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstStepRebase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactMultiplicationRowMapEdge
open PASoundness.PAtoCompactFixedFirstLocalSuccessorClosed
open PASoundness.PAtoCompactRawSuccessorBinderBridge
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Named syntax for the old local step; its map premise is unchanged. -/
def original : Formula := .imp mapBijection (.imp (namedSuccessor 0 1 2)
  (.imp rowPredicate (replace 0 1 rowPredicate)))

/-- Capture-safe specialization of both endpoint names; the successor test
binder remains 2 during this substitution. -/
def inductionInstance : Formula := replace 1 205 (replace 0 204 original)

/-- The exact specialized syntax. The first and second endpoint replacements
leave the supplied map guard fixed and do not rename its internal binders. -/
theorem induction_instance_shape : inductionInstance =
    .imp mapBijection (.imp (namedSuccessor 204 205 2)
      (.imp (replace 0 204 rowPredicate) (replace 0 205 rowPredicate))) := by decide

/-- Reindex a supplied finite K derivation of the exact original local step. -/
def rebase (h : KDerivation original.encode) : KDerivation inductionInstance.encode := by
  have h1 : KDerivation (replace 0 204 original).encode :=
    .mp (.generalize 0 h) (universalInstance 0 204 original (by decide) (by decide) (by decide))
  exact .mp (.generalize 1 h1)
    (universalInstance 1 205 (replace 0 204 original) (by decide) (by decide) (by decide))

/-- The actual row step at induction endpoint names, with the supplied raw
successor's test binder 208 converted separately to 2. -/
def local_successor_204 : KDerivation (imp mapBijection.encode
    (imp (successorCode 204 205 208)
      (imp (replace 0 204 rowPredicate).encode (replace 0 205 rowPredicate).encode))) := by
  have h0 : KDerivation original.encode := by
    change KDerivation (imp mapBijection.encode (imp (successorCode 0 1 2)
      (imp rowPredicate.encode (replace 0 1 rowPredicate).encode)))
    exact local_successor
  have h1 := rebase h0
  rw [induction_instance_shape] at h1
  change KDerivation (imp mapBijection.encode (imp (successorCode 204 205 2)
    (imp (replace 0 204 rowPredicate).encode (replace 0 205 rowPredicate).encode))) at h1
  have hs := raw_successor_rename 204 205 208 2 (by decide) (by decide) (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(replace 0 204 rowPredicate).encode, successorCode 204 205 208, mapBijection.encode]
  have hp : Context Γ (replace 0 204 rowPredicate).encode := .head _ _
  have hsucc : Context Γ (successorCode 204 205 208) := .hypothesis (by simp [Γ])
  have hm : Context Γ mapBijection.encode := .hypothesis (by simp [Γ])
  exact .mp hp (.mp (.mp hsucc (.closed hs)) (.mp hm (.closed h1)))

theorem rebase_certificate (h : KDerivation original.encode) :
    theoremCode (certificate (rebase h)) = inductionInstance.encode := certificate_correct (rebase h)

theorem local_successor_204_certificate : theoremCode (certificate local_successor_204) =
    imp mapBijection.encode (imp (successorCode 204 205 208)
      (imp (replace 0 204 rowPredicate).encode (replace 0 205 rowPredicate).encode)) :=
  certificate_correct local_successor_204
end PASoundness.PAtoCompactFixedFirstStepRebase
#print axioms PASoundness.PAtoCompactFixedFirstStepRebase.induction_instance_shape
#print axioms PASoundness.PAtoCompactFixedFirstStepRebase.rebase
#print axioms PASoundness.PAtoCompactFixedFirstStepRebase.rebase_certificate
#print axioms PASoundness.PAtoCompactFixedFirstStepRebase.local_successor_204
#print axioms PASoundness.PAtoCompactFixedFirstStepRebase.local_successor_204_certificate
