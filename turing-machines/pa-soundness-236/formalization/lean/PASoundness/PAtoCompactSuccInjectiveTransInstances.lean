import PASoundness.PAtoCompactQuotientLeftTransAtWitness

/-! Capture-safe instances of candidate-restricted K transitivity for the
quotient-successor injectivity chain. Both candidate and equivalence premises
remain explicit; no quotient-successor witness elimination is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccInjectiveTransInstances
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateSymmetryObject
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactQuotientLeftTransAtWitness
open PASoundness.PAtoCompactCompositionSharedTransitivity
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def E07 : Formula := replace 1 7 equivalentFormula
def E78 : Formula := replace 0 7 (replace 1 8 equivalentFormula)
def E08 : Formula := replace 1 8 equivalentFormula
def E81 : Formula := replace 0 8 equivalentFormula

def firstBody : Formula := replace 1 7 transBody

theorem first_syntax : firstBody = .imp (namedSymmetryCandidate 0)
    (.imp E07 (.imp E78 E08)) := by decide

/-- Candidate-guarded K transitivity at the displayed names: E(0,7) and
E(7,8) imply E(0,8). -/
def trans_first : KDerivation
    (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp E07.encode (imp E78.encode E08.encode))) := by
  have hall : KDerivation (allCode 1 transBody.encode) := by
    rw [trans_body_code]
    exact .generalize 1 shared_candidate_transitivity
  have hi := universalInstance 1 7 transBody (by decide) (by decide) (by decide)
  change KDerivation (imp (allCode 1 transBody.encode) firstBody.encode) at hi
  have h : KDerivation firstBody.encode := .mp hall hi
  rw [first_syntax] at h
  exact h

def swappedBody : Formula := replace 50 1 (replace 1 8 (replace 8 50 transBody))

theorem swapped_syntax : swappedBody = .imp (namedSymmetryCandidate 0)
    (.imp E08 (.imp E81 equivalentFormula)) := by decide

/-- Candidate-guarded K transitivity after swapping the two free endpoint
names through a fresh intermediate name 50. -/
def trans_second : KDerivation
    (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp E08.encode (imp E81.encode equivalentFormula.encode))) := by
  have h8 := universalInstance 8 50 transBody (by decide) (by decide) (by decide)
  have d8 : KDerivation (replace 8 50 transBody).encode := by
    apply KDerivation.mp (.generalize 8 ?_) h8
    simpa only [trans_body_code] using shared_candidate_transitivity
  have h1 := universalInstance 1 8 (replace 8 50 transBody)
    (by decide) (by decide) (by decide)
  have d1 : KDerivation (replace 1 8 (replace 8 50 transBody)).encode :=
    .mp (.generalize 1 d8) h1
  have h50 := universalInstance 50 1 (replace 1 8 (replace 8 50 transBody))
    (by decide) (by decide) (by decide)
  have d50 : KDerivation swappedBody.encode := .mp (.generalize 50 d1) h50
  rw [swapped_syntax] at d50
  exact d50

theorem trans_first_certificate : theoremCode (certificate trans_first) =
    imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp E07.encode (imp E78.encode E08.encode)) := certificate_correct trans_first

theorem trans_second_certificate : theoremCode (certificate trans_second) =
    imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp E08.encode (imp E81.encode equivalentFormula.encode)) := certificate_correct trans_second

end PASoundness.PAtoCompactSuccInjectiveTransInstances

#print axioms PASoundness.PAtoCompactSuccInjectiveTransInstances.trans_first
#print axioms PASoundness.PAtoCompactSuccInjectiveTransInstances.trans_second
