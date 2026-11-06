import Shared.Beeping.NPcoNP.Source284CertificateGrammar
import Shared.Beeping.NPcoNP.Source284CanonicalPairWindow

/-! Relate the bit-by-bit certificate grammar to the mathematical fixed-window
decoder without imposing a witness-length cutoff. The supplied window is
finite and explicit. This is a syntax theorem, not an implementation of the
complete prefix checker, timer, rewind, or verifier. -/

namespace Shared.Beeping.NPcoNP.Source284GrammarWindowBridge

open Shared.Beeping.NPcoNP.Source284CertificateGrammar
open Shared.Beeping.NPcoNP.Source284CanonicalPairWindow

/-- With fuel at least the number of bits, the bounded list decoder has no
effective witness-length restriction. -/
def decodeUncapped (bs : List Bool) : Option (List Bool) :=
  decodeWitness bs.length bs

theorem scan_padding (bs : List Bool) :
    scanState 3 bs = if zeros bs then 3 else 4 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | false => simpa [scanState, next, zeros] using ih
      | true => simp [scanState, next, zeros, sink_stable]

theorem decoder_iff_grammar (fuel : Nat) (bs : List Bool) (h : bs.length ≤ fuel) :
    (decodeWitness fuel bs).isSome = true ↔
      scanState 0 bs = 0 ∨ scanState 0 bs = 3 := by
  induction fuel generalizing bs with
  | zero =>
      have : bs = [] := by simpa using h
      subst bs
      decide
  | succ fuel ih =>
      cases bs with
      | nil => simp [decodeWitness, scanState]
      | cons a rest =>
          cases a with
          | false =>
              cases hz : zeros rest <;>
                simp [decodeWitness, scanState, next, scan_padding, hz]
          | true =>
              cases rest with
              | nil => simp [decodeWitness, scanState, next]
              | cons b rest =>
                  cases rest with
                  | nil => cases b <;> simp [decodeWitness, scanState, next]
                  | cons t tail =>
                      cases t with
                      | true =>
                          cases b <;> simp [decodeWitness, scanState, next, sink_stable]
                      | false =>
                          have ht : tail.length ≤ fuel := by simp at h; omega
                          cases b <;> simpa [decodeWitness, scanState, next] using ih tail ht

theorem uncapped_iff_grammar (bs : List Bool) :
    (decodeUncapped bs).isSome = true ↔
      scanState 0 bs = 0 ∨ scanState 0 bs = 3 := by
  exact decoder_iff_grammar bs.length bs le_rfl

/-- The accepted finite window is exactly a complete canonical Boolean-list
encoding followed by zero padding. Incomplete triples are rejected at the
actual window boundary, rather than completed by hypothetical extra cells. -/
theorem grammar_iff_encoded (bs : List Bool) :
    (scanState 0 bs = 0 ∨ scanState 0 bs = 3) ↔
      ∃ (w padding : List Bool), bs = BitstringEncoding.bitEncode w ++ padding ∧
        zeros padding = true := by
  constructor
  · intro h
    have hs := (uncapped_iff_grammar bs).2 h
    cases hd : decodeUncapped bs with
    | none => simp [hd] at hs
    | some w =>
        have hd' : decodeWitness bs.length bs = some w := hd
        obtain ⟨_, padding, he, hz⟩ := decodeWitness_sound bs.length bs w hd'
        exact ⟨w, padding, he, hz⟩
  · rintro ⟨w, padding, he, hz⟩
    have hw : w.length ≤ bs.length := by
      rw [he, List.length_append, Shared.ComplexityBridge.bitstring_list_encoded_length]
      omega
    have hd := decodeWitness_complete bs.length w padding hw hz
    rw [← he] at hd
    have hs : (decodeUncapped bs).isSome = true := by
      unfold decodeUncapped
      rw [hd]
      rfl
    exact (uncapped_iff_grammar bs).1 hs

/-- A correct public prefix and an accepting grammar mode characterize an
uncapped canonical pair with only zero padding in the supplied window. -/
theorem pair_grammar_iff_encoded (x bs : List Bool) :
    (bs.take (Shared.Beeping.NPcoNP.Source284PairPrefixLoader.pairPrefix x).length =
        Shared.Beeping.NPcoNP.Source284PairPrefixLoader.pairPrefix x ∧
      (scanState 0 (bs.drop (Shared.Beeping.NPcoNP.Source284PairPrefixLoader.pairPrefix x).length) = 0 ∨
       scanState 0 (bs.drop (Shared.Beeping.NPcoNP.Source284PairPrefixLoader.pairPrefix x).length) = 3)) ↔
      ∃ (w padding : List Bool), bs = BitstringEncoding.bitEncode (x,w) ++ padding ∧
        zeros padding = true := by
  let pref := Shared.Beeping.NPcoNP.Source284PairPrefixLoader.pairPrefix x
  constructor
  · rintro ⟨hp, hg⟩
    obtain ⟨w, padding, hs, hz⟩ := (grammar_iff_encoded (bs.drop pref.length)).1 hg
    refine ⟨w, padding, ?_, hz⟩
    calc
      bs = bs.take pref.length ++ bs.drop pref.length :=
        (List.take_append_drop _ _).symm
      _ = pref ++ (BitstringEncoding.bitEncode w ++ padding) := by rw [hp, hs]
      _ = BitstringEncoding.bitEncode (x,w) ++ padding := by
        rw [Shared.Beeping.NPcoNP.Source284PairPrefixLoader.pair_bits, List.append_assoc]
  · rintro ⟨w, padding, he, hz⟩
    rw [Shared.Beeping.NPcoNP.Source284PairPrefixLoader.pair_bits] at he
    rw [he]
    constructor
    · simp [pref]
    · simp only [List.append_assoc, List.drop_append_length]
      exact (grammar_iff_encoded _).2 ⟨w, padding, rfl, hz⟩

theorem encoded_length_le (bs : List Bool)
    (h : scanState 0 bs = 0 ∨ scanState 0 bs = 3) :
    ∃ w padding : List Bool,
      bs = BitstringEncoding.bitEncode w ++ padding ∧ zeros padding = true ∧
        (BitstringEncoding.bitEncode w).length ≤ bs.length := by
  obtain ⟨w, padding, he, hz⟩ := (grammar_iff_encoded bs).1 h
  refine ⟨w, padding, he, hz, ?_⟩
  rw [he, List.length_append]
  omega

example : decodeUncapped [true] = none := by decide
example : decodeUncapped [true, false] = none := by decide
example : decodeUncapped [true, false, false] = some [false] := by decide
example : decodeUncapped [false, true] = none := by decide

end Shared.Beeping.NPcoNP.Source284GrammarWindowBridge
