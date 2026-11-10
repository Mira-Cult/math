import PASoundness.PAtoCompactPartialInverseInductionCompose
import PASoundness.PAtoCompactPartialInverseAtSource
import PASoundness.PAtoCompactPartialInverseBijectionSymmetry

/-! Source specialization and restricted symmetry from a supplied literal K
candidate-induction derivation. The proof argument and candidate-source guard
are explicit: this module does not claim either unguarded inverse existence
or a PA interpretation. Named bottom remains literal compact code 1. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseCandidateProjection
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoSwap
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactPartialInversePredicate
open PASoundness.PAtoCompactPartialInverseInductionCompose PASoundness.PAtoCompactPartialInverseAtSource
open PASoundness.PAtoCompactPartialInverseFullProjection PASoundness.PAtoCompactRestrictedInverseFirst
open PASoundness.PAtoCompactPartialInverseBijectionSymmetry
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

theorem source_fresh_graph : 6 ∉ (namedCandidate 0).names := by decide

/-- Specialize the supplied candidate-induction derivation at source 0 and
project its same existential graph witness to the restricted correspondence. -/
def candidate_source_inverse (hi : KDerivation inductionPremise) : KDerivation
    (imp bijectionFormula.encode (imp (namedCandidate 0).encode
      (existsCode 7 restrictedInverseMatrix.encode))) := by
  have h8 : KDerivation (imp bijectionFormula.encode
      (imp (candidateCode 8 37 32 33 34 30 35 10 36)
        (replace 30 8 predicate).encode)) := by
    simpa only [instance_roundtrip, original, Formula.encode, candidatePrefix] using candidate_inverse_from_induction hi
  have hp := specialize_to_source h8
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(namedCandidate 0).encode,bijectionFormula.encode]
  have hc : Context Γ (namedCandidate 0).encode := Context.head [bijectionFormula.encode] _
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ (existsCode 7 fullPrefix.encode) := .mp hc (.mp hb (.closed hp))
  exact .mp hf (.closed full_prefix_exists_to_restricted_exists)

/-- Generalize the original graph only after deriving candidate-source
vacuity at 6. The candidate-induction proof remains an explicit argument. -/
def candidate_inverse_family (hi : KDerivation inductionPremise) : KDerivation
    (imp (namedCandidate 0).encode bijectionInversePremise) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(namedCandidate 0).encode]
  have hc : Context Γ (namedCandidate 0).encode := Context.head [] _
  have hp : Context Γ (imp bijectionFormula.encode (existsCode 7 restrictedInverseMatrix.encode)) := by
    apply Context.deduction
    have hb : Context (bijectionFormula.encode :: Γ) bijectionFormula.encode := Context.head _ _
    exact .mp (Context.under hc _) (.mp hb (.closed (candidate_source_inverse hi)))
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 6 q)) := by
    intro q hq
    have he : q = (namedCandidate 0).encode := by simpa [Γ] using hq
    subst q
    exact (namedCandidate 0).vacuity 6 source_fresh_graph
  exact Context.generalize 6 hv hp

/-- Conditional candidate-restricted symmetry. It requires the displayed
candidate-source hypothesis and an actual K induction proof `hi`. -/
def candidate_source_symmetry (hi : KDerivation inductionPremise) : KDerivation
    (imp (namedCandidate 0).encode (imp equivalentFormula.encode reverseEquivalent.encode)) :=
  compose (candidate_inverse_family hi) symmetry_of_bijection_inverses

theorem candidate_source_symmetry_certificate (hi : KDerivation inductionPremise) :
    theoremCode (certificate (candidate_source_symmetry hi)) =
      imp (namedCandidate 0).encode (imp equivalentFormula.encode reverseEquivalent.encode) :=
  certificate_correct (candidate_source_symmetry hi)

end PASoundness.PAtoCompactPartialInverseCandidateProjection

#print axioms PASoundness.PAtoCompactPartialInverseCandidateProjection.candidate_source_inverse
#print axioms PASoundness.PAtoCompactPartialInverseCandidateProjection.candidate_inverse_family
#print axioms PASoundness.PAtoCompactPartialInverseCandidateProjection.candidate_source_symmetry
#print axioms PASoundness.PAtoCompactPartialInverseCandidateProjection.candidate_source_symmetry_certificate
