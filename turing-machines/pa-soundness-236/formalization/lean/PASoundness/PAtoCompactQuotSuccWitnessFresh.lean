import PASoundness.PAtoCompactQuotientSuccessor
import PASoundness.PAtoCompactCandidateSymmetryObject
import PASoundness.PAtoCompactAdjunction

/-! Capture-safe quotient-successor witnesses. A direct named candidate keeps
literal code 1 as `.bottom`; its exact encoding is proved before any
substitution, avoiding replacement inside decoded self-membership. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotSuccWitnessFresh
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactQuotientSuccessor PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactGreatestSuccessor

/-- Named syntax with the exact binder order of `domainFormula`. -/
def namedDomain (x : Nat) : Formula :=
  namedBoth (namedBoth (namedTransitive x 31 32) (namedMembersTransitive x 30 31 32))
    (namedBoth (.all 33 (namedGreatestSubsetsBody x 33 34 36 37))
      (.all 33 (namedLeastSubsetsBody x 33 34 35 36 37)))

theorem namedDomain_encode (x : Nat) : (namedDomain x).encode = (domainFormula x).encode := by
  simpa only [domainFormula, encode_of_code] using
    (show (namedDomain x).encode = candidateCode x 30 31 32 33 34 35 36 37 from rfl)

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Direct named body, K-encoding equal to the literal successor body. -/
def namedBody : Formula := namedBoth (namedDomain 0)
  (namedBoth (namedDomain 1) (namedBoth (namedDomain 7)
    (namedBoth (namedSuccessor 0 7 8) (replace 0 7 equivalentFormula))))

def firstAliases : Formula := .ex 7 (replace 1 41 (replace 0 40 namedBody))
def secondAliases : Formula := .ex 7 (replace 1 43 (replace 0 42 namedBody))
def firstBody : Formula := replace 1 41 (replace 0 40 namedBody)
def secondBody : Formula := replace 1 43 (replace 0 42 namedBody)
def firstFreshBody : Formula := replace 7 0 firstBody
def secondFreshBody : Formula := replace 7 1 secondBody

/-- Exact first fresh body; the direct named domain preserves encoded bottom. -/
theorem first_body_shape : firstFreshBody = namedBoth (namedDomain 40)
    (namedBoth (namedDomain 41) (namedBoth (namedDomain 0)
      (namedBoth (namedSuccessor 40 0 8) (replace 1 41 equivalentFormula)))) := by decide

/-- Exact second fresh body, independently alpha-renamed. -/
theorem second_body_shape : secondFreshBody = namedBoth (namedDomain 42)
    (namedBoth (namedDomain 43) (namedBoth (namedDomain 1)
      (namedBoth (namedSuccessor 42 1 8)
        (replace 0 1 (replace 1 43 equivalentFormula))))) := by decide

/-- The first S instance may move its witness to fresh name 0. -/
def first_witness_alpha : KDerivation
    (imp firstAliases.encode (existsCode 0 firstFreshBody.encode)) := by
  have h := (existentialAlpha 7 0 firstBody (by decide) (by decide) (by decide)).1
  exact h

/-- The second S instance may move its witness to fresh name 1. -/
def second_witness_alpha : KDerivation
    (imp secondAliases.encode (existsCode 1 secondFreshBody.encode)) := by
  have h := (existentialAlpha 7 1 secondBody (by decide) (by decide) (by decide)).1
  exact h

theorem first_witness_alpha_certificate : theoremCode (certificate first_witness_alpha) =
    imp firstAliases.encode (existsCode 0 firstFreshBody.encode) := certificate_correct first_witness_alpha

theorem second_witness_alpha_certificate : theoremCode (certificate second_witness_alpha) =
    imp secondAliases.encode (existsCode 1 secondFreshBody.encode) := certificate_correct second_witness_alpha

end PASoundness.PAtoCompactQuotSuccWitnessFresh

#print axioms PASoundness.PAtoCompactQuotSuccWitnessFresh.first_witness_alpha
#print axioms PASoundness.PAtoCompactQuotSuccWitnessFresh.second_witness_alpha
