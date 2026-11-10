import PASoundness.PAtoCompactPartialCompositionInductionCompose
import PASoundness.CompactQuantifiers

/-! Capture-safe specialization of the candidate-prefix composition theorem
at the actual source object. The supplied global-step derivation and both
object-level input-bijection hypotheses remain explicit. This module does not
establish the step, graph collection, or quotient transitivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactPartialCompositionBase
open PASoundness.PAtoCompactPartialCompositionInductionCompose
open PASoundness.PAtoCompactConditionalTransitivityMatrix
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact candidate syntax with object name as its only varying input. -/
def namedCandidate (x : Nat) : Formula :=
  namedBoth (namedBoth (namedTransitive x 32 33) (namedMembersTransitive x 37 32 33))
    (namedBoth (.all 34 (namedGreatestSubsetsBody x 34 30 13 36))
      (.all 34 (namedLeastSubsetsBody x 34 30 35 13 36)))

theorem named_candidate_code (x : Nat) : (namedCandidate x).encode =
    candidateCode x 37 32 33 34 30 35 13 36 := by rfl

/-- The proved arbitrary-prefix statement, represented in the named syntax so
that replacing 25 by 0 is checked for capture. -/
def targetBody : Formula := .imp bijectionFormula (.imp secondBijection
  (.imp (namedCandidate 25) (.ex 9 (replace 10 25 partialComposition))))

/-- Both input graphs/domains remain as parameters; the prefix is the source. -/
def sourceBody : Formula := .imp bijectionFormula (.imp secondBijection
  (.imp (namedCandidate 0) (.ex 9 (replace 10 0 partialComposition))))

theorem body_binders_fresh : 25 ∉ targetBody.binders ∧ 0 ∉ targetBody.binders := by decide

theorem source_substitution : replace 25 0 targetBody = sourceBody := by decide

/-- From a literal K strong-step derivation, specialize candidate-domain
partial-composition existence at source 0. Neither bijection antecedent nor
the candidate antecedent is discharged. -/
def source_composition_of_step
    (step : KDerivation (imp bijectionFormula.encode (imp secondBijection.encode globalStep))) :
    KDerivation (imp bijectionFormula.encode (imp secondBijection.encode
      (imp (candidateCode 0 37 32 33 34 30 35 13 36)
        (existsCode 9 (replace 10 0 partialComposition).encode)))) := by
  have hh : KDerivation (allCode 25 targetBody.encode) := .generalize 25 (candidate_composition_of_step step)
  have hi := universalInstance 25 0 targetBody (by decide)
    body_binders_fresh.1 body_binders_fresh.2
  rw [source_substitution] at hi
  exact .mp hh hi

theorem source_composition_of_step_certificate
    (step : KDerivation (imp bijectionFormula.encode (imp secondBijection.encode globalStep))) :
    theoremCode (certificate (source_composition_of_step step)) =
      imp bijectionFormula.encode (imp secondBijection.encode
        (imp (candidateCode 0 37 32 33 34 30 35 13 36)
          (existsCode 9 (replace 10 0 partialComposition).encode))) :=
  certificate_correct (source_composition_of_step step)

end PASoundness.PAtoCompactPartialCompositionAtSource

#print axioms PASoundness.PAtoCompactPartialCompositionAtSource.source_composition_of_step
#print axioms PASoundness.PAtoCompactPartialCompositionAtSource.source_composition_of_step_certificate
