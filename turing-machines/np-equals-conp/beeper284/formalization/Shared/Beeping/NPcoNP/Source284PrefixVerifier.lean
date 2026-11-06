import Shared.Beeping.NPcoNP.Source284ReferenceComplete
import Shared.Beeping.NPcoNP.Source284HardnessFramePoly
import Shared.Beeping.NPcoNP.Source284RawParse
import Shared.Beeping.NPcoNP.Source284WitnessWindow
import Shared.Beeping.NPcoNP.Source284PositiveClock

/-! Normalize canonical NP witnesses to the source parser's finite payload.
This does not compile the verifier to a source table, enforce a source-level
cutoff, or establish candidate coverage. -/
namespace Shared.Beeping.NPcoNP.Source284PrefixVerifier

open ComplexityTheory Shared.ComplexityBridge
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Parser
open Shared.Beeping.NPcoNP.Source284RawParse
open Shared.Beeping.NPcoNP.Source284CanonicalConditional

/-- A canonical raw input with exactly the given marker/payload prefix and
no high suffix. -/
def input (xs : List Bool) : List Bool := frameBits xs []

theorem input_length (xs : List Bool) : (input xs).length = 2*xs.length+1 := by
  rw [input,Source284HardnessFrame.frameBits_length]
  simp

theorem input_isPolyTime : IsPolyTime input := by
  let reversed : List Bool → List Bool := List.reverse
  let empty : List Bool → List Bool := fun _ => []
  have hr : IsPolyTime reversed := TM2ListReverse.reverse_isPolyTime
  have he : IsPolyTime empty := TM2EmptyConstant.isPolyTime [] rfl
  have ha := TM2GuardAllStep.pair_isPolyTime reversed empty hr he
  have hp := TM2Compose.isPolyTime_comp (fun xs : List Bool => (reversed xs,empty xs))
    Source284HardnessFramePoly.produce ha Source284HardnessFramePoly.produce_isPolyTime
  have heq : (fun xs : List Bool => Source284HardnessFramePoly.produce (reversed xs,empty xs)) = input := by
    funext xs
    simp [input,reversed,empty,Source284HardnessFramePoly.produce,
      Source284HardnessFramePoly.payload,Source284HardnessFramePoly.padded,
      Source284HardnessFramePoly.zeros,Source284HardnessFramePoly.blocks_frame]
  rwa [heq] at hp

/-- The source reference depends on the parsed payload, including the virtual
zero used when the last marker has no explicit payload. -/
theorem reference_normalized (i : Nat) :
    referenceLanguage (input (payload i.bits)) =
      Shared.Beeping.NPcoNP.Source284Comparison.reference i := by
  have hp : parse (value (input (payload i.bits))) = parse i := by
    rw [input,parse_value_frameBits,← parse_value i.bits,
      Shared.Codes.BinaryAdditionCanonical.value_bits]
  simp [referenceLanguage,Shared.Beeping.NPcoNP.Source284Comparison.reference,
    Source284Parser.length,Source284Parser.description,hp]

/-- A canonical polynomial-time relation on parsed payloads, retaining the
original NP witness length bound on the canonical input. -/
def normalizedRelation (R : (List Bool × List Bool) → Bool)
    (p : List Bool × List Bool) : Bool := R (input p.1,p.2)

theorem normalizedRelation_isPolyTime (R : (List Bool × List Bool) → Bool)
    (hR : IsPolyTime R) : IsPolyTime (normalizedRelation R) := by
  let first : (List Bool × List Bool) → List Bool := fun p => p.1
  let second : (List Bool × List Bool) → List Bool := fun p => p.2
  have hf : IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hs : IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have hi : IsPolyTime (fun p : List Bool × List Bool => input (first p)) :=
    TM2Compose.isPolyTime_comp first input hf input_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : List Bool × List Bool => (input (first p),second p))
    R (TM2GuardAllStep.pair_isPolyTime _ _ hi hs) hR

/-- If the reference complement is in canonical NP, one fixed polynomial
and one polynomial-time relation work for every full numeric input. The
witness bound depends only on its parsed prefix length; no suffix bits are
silently charged to that bound. The source-level machine realization remains
separate. -/
theorem witness_of_complement_mem_NP (hNP : referenceLanguageᶜ ∈ NP) :
    ∃ (p : Polynomial Nat) (R : (List Bool × List Bool) → Bool), IsPolyTime R ∧
      ∀ i : Nat, (!Shared.Beeping.NPcoNP.Source284Comparison.reference i) = true ↔
        ∃ w : List Bool, w.length ≤ p.eval (2*Source284Parser.length i+1) ∧
          R (payload i.bits,w) = true := by
  obtain ⟨p,R,hR,hcorrect⟩ := hNP
  refine ⟨p,normalizedRelation R,normalizedRelation_isPolyTime R hR,?_⟩
  intro i
  have hlen : (payload i.bits).length = Source284Parser.length i := by
    have h := parse_length i.bits
    rw [Shared.Codes.BinaryAdditionCanonical.value_bits] at h
    exact h.symm
  have h := hcorrect (input (payload i.bits))
  simpa [normalizedRelation,reference_normalized,input_length,hlen] using h

/-- The same verifier can be searched through the source's numeric
certificate range when the clock covers the encoded window. The decoder
still enforces the original list cutoff, even if the outer clock is larger;
high certificate bits are permitted aliases. -/
theorem encoded_witness_of_complement_mem_NP (hNP : referenceLanguageᶜ ∈ NP) :
    ∃ (p : Polynomial Nat) (R : (List Bool × List Bool) → Bool), IsPolyTime R ∧
      ∀ i clock : Nat,
        Source284WitnessWindow.width (p.eval (2*Source284Parser.length i+1)) ≤ clock →
        ((∃ c, c < 2^clock ∧
          Source284WitnessWindow.check (p.eval (2*Source284Parser.length i+1))
            (fun w => R (payload i.bits,w)) c = true) ↔
          (!Shared.Beeping.NPcoNP.Source284Comparison.reference i) = true) := by
  obtain ⟨p,R,hR,hcorrect⟩ := witness_of_complement_mem_NP hNP
  refine ⟨p,R,hR,?_⟩
  intro i clock hclock
  rw [Source284WitnessWindow.clock_search_iff _ _ _ hclock]
  exact (hcorrect i).symm

/-- The exact certificate-window width expressed as a polynomial of the
source prefix length. -/
noncomputable def windowPolynomial (p : Polynomial Nat) : Polynomial Nat :=
  2 * p.comp (2 * Polynomial.X + 1) + 2

theorem windowPolynomial_eval (p : Polynomial Nat) (n : Nat) :
    (windowPolynomial p).eval n = Source284WitnessWindow.width (p.eval (2*n+1)) := by
  simp [windowPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
    Source284WitnessWindow.width]

/-- One exponent suffices for every positive-prefix input and for every
larger candidate number. This bounds the certificate window, not the running
time of a source-machine verifier. The one-step zero-prefix case is separate. -/
theorem encoded_witness_at_coupled_clock (hNP : referenceLanguageᶜ ∈ NP) :
    ∃ (k : Nat) (p : Polynomial Nat) (R : (List Bool × List Bool) → Bool), IsPolyTime R ∧
      ∀ j i : Nat, k ≤ j → 0 < Source284Parser.length i →
        ((∃ c, c < 2^(Source284Comparison.clock j i) ∧
          Source284WitnessWindow.check (p.eval (2*Source284Parser.length i+1))
            (fun w => R (payload i.bits,w)) c = true) ↔
          (!Source284Comparison.reference i) = true) := by
  obtain ⟨p,R,hR,hcorrect⟩ := encoded_witness_of_complement_mem_NP hNP
  obtain ⟨k,hk⟩ := Source284Comparison.positive_prefix_polynomial_bound (windowPolynomial p)
  refine ⟨k,p,R,hR,?_⟩
  intro j i hj hi
  have hc : Source284WitnessWindow.width (p.eval (2*Source284Parser.length i+1)) ≤
      Source284Comparison.clock j i := by
    simpa only [windowPolynomial_eval] using hk j i hj hi
  exact hcorrect i _ hc

end Shared.Beeping.NPcoNP.Source284PrefixVerifier
