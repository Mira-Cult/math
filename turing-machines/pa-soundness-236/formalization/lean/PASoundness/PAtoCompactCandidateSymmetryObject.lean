import PASoundness.PAtoCompactCandidateExact
import PASoundness.PAtoCompactOrderIsoSwap

/-! Capture-safe specialization of the candidate-restricted symmetry
derivation from object name 0 to the common object name 8. The input is
explicit K proof data; the candidate's other binders are not identified with
the differently named reflexivity candidate. No transitivity, congruence, or
PA proof translation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateSymmetryObject
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactGreatestSuccessor
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactOrderIsoSwap

/-- The named candidate formula used by the exact symmetry derivation. -/
def namedSymmetryCandidate (x : Nat) : Formula :=
  namedBoth (namedBoth (namedTransitive x 32 33) (namedMembersTransitive x 37 32 33))
    (namedBoth (.all 34 (namedGreatestSubsetsBody x 34 30 10 36))
      (.all 34 (namedLeastSubsetsBody x 34 30 35 10 36)))

theorem named_candidate_code (x : Nat) : (namedSymmetryCandidate x).encode =
    candidateCode x 37 32 33 34 30 35 10 36 := by rfl

/-- The exact source symmetry implication as a named formula. -/
def sourceBody : Formula := .imp (namedSymmetryCandidate 0)
  (.imp equivalentFormula reverseEquivalent)

/-- Isomorphism with the common object in the left and right positions. -/
def equivalentEightOne : Formula := replace 0 8 equivalentFormula
def equivalentOneEight : Formula := replace 0 8 reverseEquivalent

theorem body_binders_fresh : 0 ∉ sourceBody.binders ∧ 8 ∉ sourceBody.binders := by decide
theorem body_substitution : replace 0 8 sourceBody = .imp (namedSymmetryCandidate 8)
    (.imp equivalentEightOne equivalentOneEight) := by decide

/-- The reversed target is exactly the simultaneous capture-safe placement
of the other object at name 0's former position and object 8 at name 1. -/
theorem reversed_target_syntax : equivalentOneEight =
    replace 0 1 (replace 1 8 equivalentFormula) := by decide

/-- From the literal symmetry derivation at source name 0, construct the
literal implication for source name 8, with the second object still name 1. -/
def specialize_symmetry
    (h : KDerivation (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp equivalentFormula.encode reverseEquivalent.encode))) :
    KDerivation (imp (candidateCode 8 37 32 33 34 30 35 10 36)
      (imp equivalentEightOne.encode equivalentOneEight.encode)) := by
  have hh : KDerivation (allCode 0 sourceBody.encode) := .generalize 0 h
  have hi := universalInstance 0 8 sourceBody (by decide) body_binders_fresh.1 body_binders_fresh.2
  rw [body_substitution] at hi
  exact .mp hh hi

theorem specialize_symmetry_certificate
    (h : KDerivation (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp equivalentFormula.encode reverseEquivalent.encode))) :
    theoremCode (certificate (specialize_symmetry h)) =
      imp (candidateCode 8 37 32 33 34 30 35 10 36)
        (imp equivalentEightOne.encode equivalentOneEight.encode) :=
  certificate_correct (specialize_symmetry h)

end PASoundness.PAtoCompactCandidateSymmetryObject

#print axioms PASoundness.PAtoCompactCandidateSymmetryObject.specialize_symmetry
#print axioms PASoundness.PAtoCompactCandidateSymmetryObject.specialize_symmetry_certificate
