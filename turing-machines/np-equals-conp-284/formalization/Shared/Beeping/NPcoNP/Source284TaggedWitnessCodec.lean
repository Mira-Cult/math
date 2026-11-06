import Shared.Beeping.NPcoNP.Source284WitnessWindowComputable

/-! A two-zero low-bit tag for the witness-window representation. The tag
provides a potential boundary for a return scan. Decoding truncates the
quotient to a fixed window, while a raw scanner can continue into high bits;
no connection between arbitrary scanner runs and this decoder is proved here.
This file proves executable encoding and bounded-search semantics, not a
source table, runtime bound, or physical-machine refinement. -/

namespace Shared.Beeping.NPcoNP.Source284TaggedWitnessCodec

open Shared.Beeping.NPcoNP.Source284WitnessWindow
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Parser (frameBits)

def encode (w : List Bool) : Nat := 4 * Source284WitnessWindow.encode w

def decode (limit certificate : Nat) : Option (List Bool) :=
  if certificate % 4 = 0 then Source284WitnessWindow.decode limit (certificate / 4)
  else none

def check (limit : Nat) (predicate : List Bool → Bool) (certificate : Nat) : Bool :=
  match decode limit certificate with
  | none => false
  | some w => predicate w

/-- The first two low-order bits are zero, followed by the original frame. -/
theorem encode_bits (w : List Bool) :
    encode w = value (false :: false :: frameBits w [true]) := by
  simp [encode, Source284WitnessWindow.encode, value]
  omega

theorem decode_encode (limit : Nat) (w : List Bool) (hw : w.length ≤ limit) :
    decode limit (encode w) = some w := by
  simp [decode, encode, Source284WitnessWindow.decode_encode limit w hw]

theorem decode_length (limit certificate : Nat) (w : List Bool)
    (h : decode limit certificate = some w) : w.length ≤ limit := by
  unfold decode at h
  split_ifs at h with ht
  exact Source284WitnessWindow.decode_length limit (certificate / 4) w h

/-- A bounded witness fits in the original window plus exactly two tag bits. -/
theorem encode_lt (limit : Nat) (w : List Bool) (hw : w.length ≤ limit) :
    encode w < 2 ^ (width limit + 2) := by
  have h := Source284WitnessWindow.encode_lt limit w hw
  simp only [Nat.pow_add, show 2 ^ 2 = 4 by decide]
  unfold encode
  omega

/-- A larger numeric search cannot admit a decoded witness beyond the
original cutoff. High-bit aliases may still be accepted. -/
theorem clock_search_iff (limit clock : Nat) (predicate : List Bool → Bool)
    (hclock : width limit + 2 ≤ clock) :
    (∃ c, c < 2 ^ clock ∧ check limit predicate c = true) ↔
      ∃ w, w.length ≤ limit ∧ predicate w = true := by
  constructor
  · rintro ⟨c, _, hc⟩
    cases h : decode limit c with
    | none => simp [check, h] at hc
    | some w =>
      exact ⟨w, decode_length limit c w h, by simpa [check, h] using hc⟩
  · rintro ⟨w, hw, hp⟩
    refine ⟨encode w, lt_of_lt_of_le (encode_lt limit w hw)
      (Nat.pow_le_pow_right (by decide) hclock), ?_⟩
    simpa [check, decode_encode limit w hw] using hp

theorem encode_primrec : Primrec encode :=
  Primrec.nat_mul.comp (Primrec.const 4) Source284WitnessWindow.encode_primrec

theorem decode_primrec : Primrec₂ decode := by
  have hmod : Primrec (fun p : Nat × Nat => p.2 % 4) :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const 4)
  have hdiv : Primrec (fun p : Nat × Nat => p.2 / 4) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 4)
  have hdec : Primrec (fun p : Nat × Nat => Source284WitnessWindow.decode p.1 (p.2 / 4)) :=
    Source284WitnessWindow.decode_primrec.comp Primrec.fst hdiv
  have htest : PrimrecPred (fun p : Nat × Nat => p.2 % 4 = 0) := by
    simpa only [Nat.le_zero] using (Primrec.nat_le.comp hmod (Primrec.const 0))
  exact (Primrec.ite htest hdec (Primrec.const none)).to₂

theorem encode_computable : Computable encode := encode_primrec.to_comp
theorem decode_computable : Computable₂ decode := decode_primrec.to_comp

end Shared.Beeping.NPcoNP.Source284TaggedWitnessCodec
