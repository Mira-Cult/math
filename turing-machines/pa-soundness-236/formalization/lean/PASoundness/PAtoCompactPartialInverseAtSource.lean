import PASoundness.PAtoCompactPartialInversePredicate
import PASoundness.PAtoCompactPartialInverseFullProjection
import PASoundness.PAtoCompactCandidateExact
import PASoundness.CompactQuantifiers

/-! Specialize a supplied candidate-domain partial-inverse theorem from a
fresh target name to the source object itself. The forward bijection and
candidate-domain conditions remain explicit object-level antecedents. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseAtSource
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactPartialInversePredicate
open PASoundness.PAtoCompactPartialInverseFullProjection
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Named representation of the precise fixed candidate with only its object
name as an argument. Other displayed labels are binding names. -/
def namedCandidate (x : Nat) : Formula :=
  namedBoth (namedBoth (namedTransitive x 32 33) (namedMembersTransitive x 37 32 33))
    (namedBoth (.all 34 (namedGreatestSubsetsBody x 34 30 10 36))
      (.all 34 (namedLeastSubsetsBody x 34 30 35 10 36)))

theorem named_candidate_code (x : Nat) : (namedCandidate x).encode =
    candidateCode x 37 32 33 34 30 35 10 36 := by rfl

/-- The fresh-target theorem written as one named formula for sound, literal
K universal instantiation. -/
def targetBody : Formula := .imp bijectionFormula
  (.imp (namedCandidate 8) (replace 30 8 predicate))

def sourceBody : Formula := .imp bijectionFormula
  (.imp (namedCandidate 0) (.ex 7 fullPrefix))

theorem body_names : 8 ∉ targetBody.binders ∧ 0 ∉ targetBody.binders := by decide

theorem source_substitution : replace 8 0 targetBody = sourceBody := by decide

/-- Given a K proof for arbitrary object 8, instantiate that theorem at the
source object 0. Bijection and candidate hypotheses are not discharged. -/
def specialize_to_source
    (h : KDerivation (imp bijectionFormula.encode
      (imp (candidateCode 8 37 32 33 34 30 35 10 36)
        (replace 30 8 predicate).encode))) :
    KDerivation (imp bijectionFormula.encode
      (imp (candidateCode 0 37 32 33 34 30 35 10 36)
        (existsCode 7 fullPrefix.encode))) := by
  have hh : KDerivation (allCode 8 targetBody.encode) := .generalize 8 h
  have hi := universalInstance 8 0 targetBody (by decide) body_names.1 body_names.2
  rw [source_substitution] at hi
  exact .mp hh hi

theorem specialize_to_source_certificate
    (h : KDerivation (imp bijectionFormula.encode
      (imp (candidateCode 8 37 32 33 34 30 35 10 36)
        (replace 30 8 predicate).encode))) :
    theoremCode (certificate (specialize_to_source h)) =
      imp bijectionFormula.encode
        (imp (candidateCode 0 37 32 33 34 30 35 10 36)
          (existsCode 7 fullPrefix.encode)) :=
  certificate_correct (specialize_to_source h)

end PASoundness.PAtoCompactPartialInverseAtSource

#print axioms PASoundness.PAtoCompactPartialInverseAtSource.specialize_to_source
#print axioms PASoundness.PAtoCompactPartialInverseAtSource.specialize_to_source_certificate
