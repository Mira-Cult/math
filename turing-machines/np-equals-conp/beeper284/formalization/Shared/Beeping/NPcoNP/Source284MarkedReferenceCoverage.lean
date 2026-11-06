import Shared.Beeping.NPcoNP.Source284MarkedCanonicalCandidate
import Shared.Beeping.NPcoNP.Source284PrefixVerifier

/-! Positive-prefix coverage for the actual 284 reference complement.
The zero-prefix, one-step candidate case remains separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284MarkedReferenceCoverage

open ComplexityTheory Shared.ComplexityBridge
open Shared.ComplexityBridge.CanonicalClasses
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

def prefixComplement : DecisionProblem := fun x => referenceLanguageᶜ (Source284PrefixVerifier.input x)

theorem prefixComplement_mem_NP (h : referenceLanguageᶜ ∈ NP) : prefixComplement ∈ NP := by
  apply TM2PairMap.np_pullback_closed prefixComplement referenceLanguageᶜ h
  exact ⟨Source284PrefixVerifier.input,Source284PrefixVerifier.input_isPolyTime,fun _ => rfl⟩

theorem prefixComplement_frame (x : List Bool) (suffix : Nat) :
    prefixComplement x = !reference (encodeFrame x suffix) := by
  have h := Source284PrefixVerifier.reference_normalized (encodeFrame x suffix)
  rw [Source284NormalizedWindow.payload_encodeFrame] at h
  change (! (referenceLanguage (Source284PrefixVerifier.input x))) = (! (reference (encodeFrame x suffix)))
  rw [h]

/-- If the actual reference complement is in canonical NP, one fixed
candidate agrees with it on every positive decoded prefix, for arbitrary
higher source input bits. -/
theorem positive_reference_coverage (h : referenceLanguageᶜ ∈ NP) (threshold : Nat) :
    ∃ j : Nat, threshold < j ∧ ∀ i : Nat, 0 < Source284Parser.length i →
      candidate j i = !reference i := by
  obtain ⟨j,hj,hcandidate⟩ := Source284MarkedCanonicalCandidate.canonical_np_positive_candidate
    prefixComplement (prefixComplement_mem_NP h) threshold
  refine ⟨j,hj,?_⟩
  intro i hi
  obtain ⟨x,suffix,hframe⟩ := Source284Parser.encodeFrame_surjective i
  have hlen : Source284Parser.length i = x.length := by
    rw [← hframe]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  have hx : 0 < x.length := by omega
  have hc := hcandidate x suffix hx
  have hL := prefixComplement_frame x suffix
  rw [hframe] at hc hL
  rw [hL] at hc
  cases hbit : candidate j i <;> cases hreference : reference i <;> simp_all

/-- Canonical NP = coNP supplies the actual reference-complement hypothesis,
so the source has one arbitrarily large candidate correct on positive
prefixes. The empty-prefix case is not included in this statement. -/
theorem classes_imply_positive_reference_coverage (h : NP = coNP) (threshold : Nat) :
    ∃ j : Nat, threshold < j ∧ ∀ i : Nat, 0 < Source284Parser.length i →
      candidate j i = !reference i :=
  positive_reference_coverage (Source284ReferenceHard.reference_complement_iff_classes.mpr h) threshold

end Shared.Beeping.NPcoNP.Source284MarkedReferenceCoverage
