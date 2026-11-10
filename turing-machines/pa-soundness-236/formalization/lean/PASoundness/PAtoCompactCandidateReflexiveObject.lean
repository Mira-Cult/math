import PASoundness.PAtoCompactCandidateReflexivity

/-! Capture-safe specialization of the reflexivity proof to object name 8.
Name 0 remains a binder in the candidate, so substitution 30→0 is not used.
This does not align the symmetry candidate's other binders or prove quotient
transitivity, congruence, or a PA interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateReflexiveObject
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactGreatestSuccessor PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateReflexivity
open PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport

def namedReflexiveCandidate (x : Nat) : Formula :=
  namedBoth (namedBoth (namedTransitive x 37 38) (namedMembersTransitive x 41 37 38))
    (namedBoth (.all 32 (namedGreatestSubsetsBody x 32 0 34 35))
      (.all 32 (namedLeastSubsetsBody x 32 0 31 34 35)))

theorem named_candidate_encode (x : Nat) : (namedReflexiveCandidate x).encode =
    candidateCode x 41 37 38 32 0 31 34 35 := by rfl

def sourceBody : Formula := .imp (namedReflexiveCandidate 30) reflexive30
def reflexive8 : Formula := replace 30 8 reflexive30

theorem body_binders_fresh : 30 ∉ sourceBody.binders ∧ 8 ∉ sourceBody.binders := by decide
theorem body_substitution : replace 30 8 sourceBody = .imp (namedReflexiveCandidate 8) reflexive8 := by decide

/-- The literal reflexivity proof specializes to a third object name 8,
without substituting the candidate's bound name 0. -/
def reflexivity_at_eight : KDerivation
    (imp (candidateCode 8 41 37 38 32 0 31 34 35) reflexive8.encode) := by
  have hh : KDerivation (allCode 30 sourceBody.encode) := .generalize 30 candidate_reflexive
  have hi := universalInstance 30 8 sourceBody (by decide) body_binders_fresh.1 body_binders_fresh.2
  rw [body_substitution] at hi
  exact .mp hh hi

theorem reflexivity_at_eight_certificate : theoremCode (certificate reflexivity_at_eight) =
    imp (candidateCode 8 41 37 38 32 0 31 34 35) reflexive8.encode :=
  certificate_correct reflexivity_at_eight

end PASoundness.PAtoCompactCandidateReflexiveObject

#print axioms PASoundness.PAtoCompactCandidateReflexiveObject.reflexivity_at_eight
#print axioms PASoundness.PAtoCompactCandidateReflexiveObject.reflexivity_at_eight_certificate
