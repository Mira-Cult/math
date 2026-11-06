import Shared.Beeping.NPcoNP.Source284SATWindowSoundness
import Shared.Beeping.NPcoNP.Source284GrammarWindowBridge

/-! An exact SAT search with the uncapped finite-window grammar used by the
developing source-table validator. All finite loops here are executable list
operations. This file does not claim that the recognizer is already linked
to a source transition table or that it supplies a polynomial-time reduction. -/

namespace Shared.Beeping.NPcoNP.Source284SATGrammarCharacterization

open Shared.Codes.FinitePrograms
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284CanonicalPairWindow
open Shared.Beeping.NPcoNP.Source284PairPrefixLoader (pairPrefix)
open Shared.Beeping.NPcoNP.Source284CertificateGrammar (scanState)
open Shared.Beeping.NPcoNP.Source284GrammarWindowBridge
open Shared.Beeping.NPcoNP.Source284SATWindowSoundness
open Shared.ComplexityBridge.BoundedHardness

/-- The same prefix and final grammar-state conditions checked by the
unrolled validator. Witness length is not capped in this SAT-only filter. -/
def validWindow (x : List Bool) (width certificate : Nat) : Bool :=
  let bits := window width certificate
  decide (bits.take (pairPrefix x).length = pairPrefix x ∧
    (scanState 0 (bits.drop (pairPrefix x).length) = 0 ∨
     scanState 0 (bits.drop (pairPrefix x).length) = 3))

/-- Every accepted window represents an actual canonical pair, irrespective
of high certificate bits or the length of the decoded witness. -/
theorem validWindow_sound (x : List Bool) (width certificate : Nat)
    (h : validWindow x width certificate = true) :
    ∃ w : List Bool, certificate % 2^width = value (BitstringEncoding.bitEncode (x,w)) := by
  have hg : (window width certificate).take (pairPrefix x).length = pairPrefix x ∧
      (scanState 0 ((window width certificate).drop (pairPrefix x).length) = 0 ∨
       scanState 0 ((window width certificate).drop (pairPrefix x).length) = 3) := by
    exact of_decide_eq_true h
  obtain ⟨w, padding, he, hz⟩ := (pair_grammar_iff_encoded x _).1 hg
  refine ⟨w, ?_⟩
  have hv := congrArg value he
  rw [window_value] at hv
  have hp := zeros_value padding hz
  rw [Shared.Beeping.NPcoNP.Source284Parser.bitValue_append] at hv
  simpa [hp] using hv

/-- A bounded list witness gives an accepted window with an explicit finite
zero tail. -/
theorem validWindow_complete (x w : List Bool) (width : Nat)
    (hw : w.length ≤ x.length) (hwidth : 9*x.length+1 ≤ width) :
    validWindow x width (value (BitstringEncoding.bitEncode (x,w))) = true := by
  have hlen : (BitstringEncoding.bitEncode (x,w)).length ≤ width := by
    rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
    omega
  unfold validWindow
  apply decide_eq_true
  apply (pair_grammar_iff_encoded x _).2
  rw [window_value_bits width _ hlen]
  exact ⟨w, _, rfl, zeros_replicate _⟩

def filtered (program : Program) (x : List Bool) (width fuel certificate : Nat) : Bool :=
  validWindow x width certificate &&
    accepts (value (Shared.Beeping.NPcoNP.Source284CompileBitsTM2.compileBits program))
      certificate 0 fuel

/-- SAT is exactly the bounded search through certificates whose finite
window passes this uncapped grammar and whose subsequent source verifier
accepts. The same fixed verifier works in both directions. -/
theorem sat_iff_grammar_search :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ (x : List Bool) (width outer : Nat),
        9*x.length+1 ≤ width → commonFuel Polynomial.X clock x ≤ width →
        width ≤ outer →
        ((∃ certificate, certificate < 2^outer ∧
          filtered program x width (commonFuel Polynomial.X clock x) certificate = true) ↔
          Shared.ComplexityBridge.CNF.sat x = true) := by
  obtain ⟨program, clock, hv, hsound, hcomplete⟩ := sat_fixed_verifier_window_sound
  refine ⟨program, clock, hv, ?_⟩
  intro x width outer hwidth hfuel houter
  constructor
  · rintro ⟨certificate, _, h⟩
    simp only [filtered, Bool.and_eq_true] at h
    obtain ⟨hvw, haccept⟩ := h
    obtain ⟨w, hwindow⟩ := validWindow_sound x width certificate hvw
    exact hsound x w _ width certificate hfuel hwindow haccept
  · intro hs
    obtain ⟨w, hw, haccept⟩ := hcomplete x hs
    let certificate := value (BitstringEncoding.bitEncode (x,w))
    have hlen : (BitstringEncoding.bitEncode (x,w)).length ≤ outer := by
      rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
      omega
    have hlt : certificate < 2^outer := by
      exact lt_of_lt_of_le
        (Shared.Beeping.NPcoNP.Source284Witness.value_lt_pow_length _)
        (Nat.pow_le_pow_right (by decide) hlen)
    refine ⟨certificate, hlt, ?_⟩
    simp [filtered, certificate, validWindow_complete x w width hw hwidth, haccept]

end Shared.Beeping.NPcoNP.Source284SATGrammarCharacterization
