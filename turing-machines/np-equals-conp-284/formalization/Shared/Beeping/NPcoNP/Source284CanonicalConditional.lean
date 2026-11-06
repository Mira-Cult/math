import Shared.Beeping.NPcoNP.Source284ComparisonBridge
import Shared.Codes.BitNumeralCompare
import Shared.ComplexityBridge.GeneratorGateListClosed
import Shared.ComplexityBridge.TM2PairMap

/-! The precise remaining canonical-class obligations for the 284 source.

The raw bit-list representation below is interpreted little-endian and allows
redundant high zero bits. It faithfully covers every natural source input; no
polynomial-time encoding or source/compiler simulation is asserted here.
The conditional theorem is about the shared *atomic* controller, not the
literal 284-state machine. Its hypotheses are the as-yet-unproved NP membership
and hardness of the source reference, NP membership of each fixed candidate,
and uniform source-code coverage of an NP verifier for the reference
complement. They are not packaged as an assumed complexity equality. -/
namespace Shared.Beeping.NPcoNP.Source284CanonicalConditional

open ComplexityTheory
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CanonicalClasses
open Shared.Beeping.NPcoNP.Source284Comparison

/-- Canonical bitstrings interpreted as source inputs, including leading-zero
aliases. This is an exact language definition, not an efficiency assertion. -/
def referenceLanguage : DecisionProblem := fun xs => reference (Shared.Codes.BitNumeralCompare.value xs)

/-- The actual source candidate, with its numeric program coupled to its
clock exponent. -/
def candidateLanguage (j : Nat) : DecisionProblem :=
  fun xs => candidate j (Shared.Codes.BitNumeralCompare.value xs)

/-- Surjectivity of the bitstring interpretation makes natural-number
agreement exactly equivalent to agreement on every raw bitstring. -/
theorem candidate_agrees_iff (j : Nat) :
    (∀ i, candidate j i = !reference i) ↔
      candidateLanguage j = referenceLanguageᶜ := by
  constructor
  · intro h
    funext xs
    exact h (Shared.Codes.BitNumeralCompare.value xs)
  · intro h i
    have hi := congrFun h (Computability.encodeNat i)
    simpa [candidateLanguage, referenceLanguage,
      Shared.Codes.BitNumeralCompare.value_encodeNat] using hi

/-- If the source reference belongs to canonical NP and SAT reduces to it,
its complement belongs to NP exactly when canonical NP equals canonical
coNP. The hardness hypothesis is a uniform polynomial many-one reduction on
all bitstrings, including malformed inputs and redundant encodings. -/
theorem reference_complement_iff_classes
    (member : referenceLanguage ∈ NP)
    (satHard : PolyRed CNF.sat referenceLanguage) :
    referenceLanguageᶜ ∈ NP ↔ NP = coNP := by
  constructor
  · intro hc
    have hsat : CNF.satᶜ ∈ NP :=
      TM2PairMap.np_pullback_closed _ _ hc (polyRed_complement satHard)
    exact (np_eq_conp_iff_complement_complete_in_np
      GeneratorGateListClosed.satComplete TM2PairMap.np_pullback_closed).2 hsat
  · intro h
    have hc : referenceLanguageᶜ ∈ coNP := by
      change (referenceLanguageᶜ)ᶜ ∈ NP
      simpa using member
    rw [h]
    exact hc

/-- The atomic source controller has the desired class characterization once
four separate, explicit source-model obligations have been discharged.
`coverage` requires a *single* candidate number whenever the complement is
in NP; its clock and program description cannot depend on the input. The
hypothesis does not assert an executable procedure for finding that number. -/
theorem controller_iff_classes
    (member : referenceLanguage ∈ NP)
    (satHard : PolyRed CNF.sat referenceLanguage)
    (candidateMember : ∀ j, candidateLanguage j ∈ NP)
    (coverage : referenceLanguageᶜ ∈ NP →
      ∃ j, candidateLanguage j = referenceLanguageᶜ) :
    (Shared.Beeping.Controller.system compare 0).EventuallySilent ↔ NP = coNP := by
  rw [controller_silent_iff]
  constructor
  · rintro ⟨j, hj⟩
    have heq := (candidate_agrees_iff j).1 hj
    have hc : referenceLanguageᶜ ∈ NP := by
      rw [← heq]
      exact candidateMember j
    exact (reference_complement_iff_classes member satHard).1 hc
  · intro h
    obtain ⟨j, hj⟩ := coverage ((reference_complement_iff_classes member satHard).2 h)
    exact ⟨j, (candidate_agrees_iff j).2 hj⟩

end Shared.Beeping.NPcoNP.Source284CanonicalConditional
