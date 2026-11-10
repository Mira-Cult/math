import PASoundness.PAtoCompactSuccessorCancellationAliased
import PASoundness.PAtoCompactQuotientSuccessor
import PASoundness.PAtoCompactCandidateAlpha
import PASoundness.PAtoCompactSuccInjectiveEquivalenceChain

/-! Composition of a raw-successor E chain with the reviewed
successor-cancellation derivation. The predecessor-domain transitivity premise
is discharged here. The output is
the existing equality-guarded E alias, not unsafe raw replacement into the
original formula. This is not yet quotient-successor witness elimination or a
complete PA interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotSuccInjectiveRaw
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateAlpha
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactQuotientSuccessor
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactEquivalentAliasInstantiation
open PASoundness.PAtoCompactEquivalentAliasGuardLift PASoundness.PAtoCompactSuccessorCancellationAliased
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def candidate0 : Nat := candidateCode 0 37 32 33 34 30 35 10 36
def candidate1 : Nat := candidateCode 1 37 32 33 34 30 35 10 36
def edge07 : Formula := replace 1 7 equivalentFormula
def edge78 : Formula := replace 0 7 (replace 1 8 equivalentFormula)
def edge18 : Formula := replace 0 1 (replace 1 8 equivalentFormula)

/-- The literal quotient-domain candidate at predecessor name 5 entails the
exact transitivity test names used by the reviewed cancellation proof. -/
def candidate5_transitive : KDerivation
    (imp (domainFormula 5).encode (transitiveCode 5 11 12)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let D := (domainFormula 5).encode
  have hd : Context [D] (candidateCode 5 30 31 32 33 34 35 36 37) := by
    simpa [D, domainFormula, CompactNamed.encode_of_code] using (Context.head [] D)
  have ht : Context [D] (transitiveCode 5 31 32) :=
    Context.conjunctionLeft (Context.conjunctionLeft hd)
  exact .mp ht (.closed (transitive_rename 5 31 32 11 12 (by decide)))

/-- Given a K proof of the indicated candidate-guarded E chain, the two raw
successor graphs, the second predecessor candidate, and the three displayed
E hypotheses entail the exact endpoint alias formula. -/
def conditional_raw_cancellation
    (chain : KDerivation (imp candidate0 (imp candidate1
      (imp edge07.encode (imp edge78.encode (imp edge18.encode equivalentFormula.encode)))))) :
    KDerivation (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (domainFormula 5).encode (imp candidate0 (imp candidate1
        (imp edge07.encode (imp edge78.encode (imp edge18.encode
          (guarded originalAliases).encode)))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := successorCode 2 0 9
  let T := successorCode 5 1 10
  let D := (domainFormula 5).encode
  let Γ := [edge18.encode,edge78.encode,edge07.encode,candidate1,candidate0,D,T,S]
  have hS : Context Γ S := .hypothesis (by simp [Γ])
  have hT : Context Γ T := .hypothesis (by simp [Γ])
  have hD : Context Γ D := .hypothesis (by simp [Γ])
  have hC0 : Context Γ candidate0 := .hypothesis (by simp [Γ])
  have hC1 : Context Γ candidate1 := .hypothesis (by simp [Γ])
  have h07 : Context Γ edge07.encode := .hypothesis (by simp [Γ])
  have h78 : Context Γ edge78.encode := .hypothesis (by simp [Γ])
  have h18 : Context Γ edge18.encode := Context.head _ _
  have he : Context Γ equivalentFormula.encode :=
    .mp h18 (.mp h78 (.mp h07 (.mp hC1 (.mp hC0 (.closed chain)))))
  have ht : Context Γ (transitiveCode 5 11 12) := .mp hD (.closed candidate5_transitive)
  exact .mp he (.mp ht (.mp hT (.mp hS (.closed successor_cancellation_aliased))))

theorem conditional_raw_cancellation_certificate
    (chain : KDerivation (imp candidate0 (imp candidate1
      (imp edge07.encode (imp edge78.encode (imp edge18.encode equivalentFormula.encode)))))) :
    theoremCode (certificate (conditional_raw_cancellation chain)) =
      imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
        (imp (domainFormula 5).encode (imp candidate0 (imp candidate1
          (imp edge07.encode (imp edge78.encode (imp edge18.encode
            (guarded originalAliases).encode))))))) :=
  certificate_correct (conditional_raw_cancellation chain)

/-- The explicit candidate-guarded chain is supplied by a finite K proof;
the displayed raw graphs and domain/equivalence hypotheses remain required. -/
def raw_cancellation :
    KDerivation (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (domainFormula 5).encode (imp candidate0 (imp candidate1
        (imp edge07.encode (imp edge78.encode (imp edge18.encode
          (guarded originalAliases).encode)))))))) := by
  apply conditional_raw_cancellation
  exact PAtoCompactSuccInjectiveEquivalenceChain.witness_equivalence

theorem raw_cancellation_certificate : theoremCode (certificate raw_cancellation) =
    imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (domainFormula 5).encode (imp candidate0 (imp candidate1
        (imp edge07.encode (imp edge78.encode (imp edge18.encode
          (guarded originalAliases).encode))))))) :=
  certificate_correct raw_cancellation

end PASoundness.PAtoCompactQuotSuccInjectiveRaw

#print axioms PASoundness.PAtoCompactQuotSuccInjectiveRaw.candidate5_transitive
#print axioms PASoundness.PAtoCompactQuotSuccInjectiveRaw.conditional_raw_cancellation
#print axioms PASoundness.PAtoCompactQuotSuccInjectiveRaw.raw_cancellation
#print axioms PASoundness.PAtoCompactQuotSuccInjectiveRaw.raw_cancellation_certificate
