import PASoundness.PAtoCompactQuotSuccWitnessFresh
import PASoundness.PAtoCompactQuotSuccRawTransport
import PASoundness.PAtoCompactQuotSuccAliasTransport
import PASoundness.PAtoCompactQuotSuccRawNormalized

/-! Local quotient-successor cancellation with both fresh witness bodies
supplied. All four endpoint equality guards and the output E premise remain
explicit; this module does not eliminate either S witness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotSuccWitnessLocal
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactQuotientSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactQuotSuccWitnessFresh PASoundness.PAtoCompactQuotSuccRawTransport
open PASoundness.PAtoCompactQuotSuccAliasTransport PASoundness.PAtoCompactQuotSuccRawNormalized
open PASoundness.PAtoCompactQuotSuccInjectiveRaw PASoundness.PAtoCompactEquivalentAliasInstantiation
open PASoundness.PAtoCompactEquivalentAliasGuardLift
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle
  PASoundness.PAtoCompactQuotientSuccessor.domainFormula

/-- Transport the second predecessor's exact named-domain formula to name 5. -/
def second_domain_transport : KDerivation
    (imp (equal 42 5) (imp (namedDomain 42).encode (domainFormula 5).encode)) := by
  have h := (equalityReplace 42 5 (namedDomain 42) (by decide) (by decide)).1
  have hs : replace 42 5 (namedDomain 42) = namedDomain 5 := by decide
  rw [hs, namedDomain_encode 5] at h
  exact h

/-- From both explicitly supplied fresh witness bodies, all endpoint alias
guards, and E(7,8), derive the guarded predecessor E conclusion. -/
def local_cancellation : KDerivation
    (imp (equal 40 2) (imp (equal 41 7) (imp (equal 42 5) (imp (equal 43 8)
      (imp edge78.encode (imp firstFreshBody.encode (imp secondFreshBody.encode
        (guarded originalAliases).encode))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondFreshBody.encode,firstFreshBody.encode,edge78.encode,
    equal 43 8,equal 42 5,equal 41 7,equal 40 2]
  have h1 : Context Γ firstFreshBody.encode := .hypothesis (by simp [Γ])
  have h2 : Context Γ secondFreshBody.encode := Context.head _ _
  have h40 : Context Γ (equal 40 2) := .hypothesis (by simp [Γ])
  have h41 : Context Γ (equal 41 7) := .hypothesis (by simp [Γ])
  have h42 : Context Γ (equal 42 5) := .hypothesis (by simp [Γ])
  have h43 : Context Γ (equal 43 8) := .hypothesis (by simp [Γ])
  have he78 : Context Γ edge78.encode := .hypothesis (by simp [Γ])
  rw [first_body_shape] at h1
  rw [second_body_shape] at h2
  change Context Γ (both (namedDomain 40).encode (both (namedDomain 41).encode
    (both (namedDomain 0).encode (both (namedSuccessor 40 0 8).encode firstAlias.encode)))) at h1
  change Context Γ (both (namedDomain 42).encode (both (namedDomain 43).encode
    (both (namedDomain 1).encode (both (namedSuccessor 42 1 8).encode secondAlias.encode)))) at h2
  have hD0 : Context Γ (domainFormula 0).encode := by
    rw [← namedDomain_encode 0]
    exact Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight h1))
  have hD1 : Context Γ (domainFormula 1).encode := by
    rw [← namedDomain_encode 1]
    exact Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight h2))
  have hD42 : Context Γ (namedDomain 42).encode := Context.conjunctionLeft h2
  have hD5 : Context Γ (domainFormula 5).encode := .mp hD42 (.mp h42 (.closed second_domain_transport))
  have htail1 := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight h1))
  have htail2 := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight h2))
  have hs : Context Γ (successorCode 2 0 9) :=
    .mp (Context.conjunctionLeft htail1) (.mp h40 (.closed first_raw_transport))
  have ht : Context Γ (successorCode 5 1 10) :=
    .mp (Context.conjunctionLeft htail2) (.mp h42 (.closed second_raw_transport))
  have he07 : Context Γ edge07.encode :=
    .mp (Context.conjunctionRight htail1) (.mp h41 (.closed first_output_transport))
  have he18 : Context Γ edge18.encode :=
    .mp (Context.conjunctionRight htail2) (.mp h43 (.closed second_output_transport))
  exact .mp he18 (.mp he78 (.mp he07 (.mp hD1 (.mp hD0 (.mp hD5 (.mp ht (.mp hs (.closed raw_normalized))))))))

theorem local_cancellation_certificate : theoremCode (certificate local_cancellation) =
    imp (equal 40 2) (imp (equal 41 7) (imp (equal 42 5) (imp (equal 43 8)
      (imp edge78.encode (imp firstFreshBody.encode (imp secondFreshBody.encode
        (guarded originalAliases).encode)))))) := certificate_correct local_cancellation

end PASoundness.PAtoCompactQuotSuccWitnessLocal

#print axioms PASoundness.PAtoCompactQuotSuccWitnessLocal.local_cancellation
#print axioms PASoundness.PAtoCompactQuotSuccWitnessLocal.local_cancellation_certificate
