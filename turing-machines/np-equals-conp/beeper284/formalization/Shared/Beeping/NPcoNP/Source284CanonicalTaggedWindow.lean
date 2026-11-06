import Shared.Beeping.NPcoNP.Source284CanonicalTaggedVerifier
import Shared.Beeping.NPcoNP.Source284PackedGuardIsolation
import Shared.Beeping.NPcoNP.Source284PrefixVerifier

/-! A fixed finite source verifier for every canonical polynomial-time pair
relation, with a polynomial cutoff and arbitrary data outside the cutoff
window. The source loader that establishes the window remains unconstructed. -/
namespace Shared.Beeping.NPcoNP.Source284CanonicalTaggedWindow

open ComplexityTheory Shared.ComplexityBridge
open Shared.Codes.FinitePrograms
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284PackedGuardWindow
open Shared.Beeping.NPcoNP.Source284PackedGuardIsolation
open Shared.Beeping.NPcoNP.Source284RawParse (payload)
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284CanonicalConditional

/-- One fixed source table implements any canonical polynomial-time relation
with its original polynomial witness cutoff. The initial finite window must
already contain the packed normalized data. The same result holds at all
later clocks, regardless of the bits outside that starting window. -/
theorem source_window_verifier (p : Polynomial Nat) (R : List Bool × List Bool → Bool)
    (hR : IsPolyTime R) :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      (∀ n, Source284WitnessWindow.width (p.eval (2*n+1))+2 ≤ clock.eval n) ∧
      ∀ (input : List Bool) (certificate : Nat) (c : Source284Relative.Config) (extra : Nat),
        let m := p.eval (2*Source284Parser.length (value input)+1)
        let packed := BitstringEncoding.bitEncode (inputBits input,certificateBits m certificate)
        Window (clock.eval (Source284Parser.length (value input))) c (Source284Relative.initial (value packed) 0) →
        ((Source284Relative.run (Source284CompileRecords.compile program) c
          (clock.eval (Source284Parser.length (value input))+extra)).state == 0) =
          Source284TaggedWitnessCodec.check m (fun w => R (payload input,w)) certificate := by
  obtain ⟨program,q,hvalid,hcorrect⟩ := Source284CanonicalTaggedVerifier.finite_program p R hR
  let bound : Polynomial Nat := Polynomial.C 12 * Polynomial.X +
    Polynomial.C 6 * p.comp (Polynomial.C 2 * Polynomial.X + Polynomial.C 1) + Polynomial.C 25
  let margin : Polynomial Nat := Polynomial.C 2 * p.comp (Polynomial.C 2 * Polynomial.X + Polynomial.C 1) + Polynomial.C 4
  let clock : Polynomial Nat := q.comp bound + margin
  refine ⟨program,clock,hvalid,?_,?_⟩
  · intro n
    simp only [clock,margin,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Source284WitnessWindow.width]
    omega
  · intro input certificate c extra
    dsimp only
    intro hw
    let m := p.eval (2*Source284Parser.length (value input)+1)
    let packed := BitstringEncoding.bitEncode (inputBits input,certificateBits m certificate)
    have hlen : packed.length ≤ bound.eval (Source284Parser.length (value input)) := by
      have h := packed_length m certificate input
      simpa [packed,bound,m,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
        Polynomial.eval_C,Polynomial.eval_X] using h
    have hclock : q.eval packed.length ≤ clock.eval (Source284Parser.length (value input)) := by
      have hmono := TM2Compose.polynomial_eval_mono q hlen
      simp only [clock,Polynomial.eval_add,Polynomial.eval_comp]
      omega
    have hsmall := hcorrect (inputBits input) (certificateBits m certificate)
    have hb := BoundedHardness.bounded_mono program packed (q.eval packed.length)
      (clock.eval (Source284Parser.length (value input)))
      (Source284CanonicalTaggedVerifier.compare p R (inputBits input,certificateBits m certificate))
      hclock hsmall
    have hh := compiled_window_stable program packed (clock.eval (Source284Parser.length (value input)))
      (Source284CanonicalTaggedVerifier.compare p R (inputBits input,certificateBits m certificate))
      hvalid hb c hw extra
    rw [Source284CanonicalTaggedVerifier.compare_correct,input_prefix_length,input_payload,
      certificateBits_value] at hh
    dsimp only [m] at hh
    rw [tagged_check_mod] at hh
    exact hh

/-- Canonical NP membership yields a fixed finite source verifier and a
polynomial window/clock for the actual complement reference. The caller's
`place` configurations are an explicit preparation obligation, not an
assertion that a finite source loader exists. -/
theorem reference_window (hNP : referenceLanguageᶜ ∈ NP) :
    ∃ (p : Polynomial Nat) (R : List Bool × List Bool → Bool) (program : Program) (clock : Polynomial Nat),
      IsPolyTime R ∧ valid program = true ∧
      (∀ n, Source284WitnessWindow.width (p.eval (2*n+1))+2 ≤ clock.eval n) ∧
      ∀ (i : Nat) (place : Nat → Source284Relative.Config),
        (∀ certificate, Window (clock.eval (Source284Parser.length i)) (place certificate)
          (Source284Relative.initial
            (value (BitstringEncoding.bitEncode
              (inputBits i.bits,certificateBits (p.eval (2*Source284Parser.length i+1)) certificate))) 0)) →
        ((∃ certificate, certificate < 2^(clock.eval (Source284Parser.length i)) ∧
          ((Source284Relative.run (Source284CompileRecords.compile program) (place certificate)
            (clock.eval (Source284Parser.length i))).state == 0) = true) ↔
          (!reference i) = true) := by
  obtain ⟨p,R,hR,hwitness⟩ := Source284PrefixVerifier.witness_of_complement_mem_NP hNP
  obtain ⟨program,clock,hvalid,hwindow,hsource⟩ := source_window_verifier p R hR
  refine ⟨p,R,program,clock,hR,hvalid,hwindow,?_⟩
  intro i place hplace
  have hv : value i.bits = i := Shared.Codes.BinaryAdditionCanonical.value_bits i
  have hc (certificate : Nat) :
      ((Source284Relative.run (Source284CompileRecords.compile program) (place certificate)
        (clock.eval (Source284Parser.length i))).state == 0) =
        Source284TaggedWitnessCodec.check (p.eval (2*Source284Parser.length i+1))
          (fun w => R (payload i.bits,w)) certificate := by
    have h := hsource i.bits certificate (place certificate) 0
    simp only [hv,Nat.add_zero] at h
    exact h (hplace certificate)
  simp_rw [hc]
  rw [Source284TaggedWitnessCodec.clock_search_iff _ _ _ (hwindow (Source284Parser.length i))]
  exact (hwitness i).symm

end Shared.Beeping.NPcoNP.Source284CanonicalTaggedWindow
