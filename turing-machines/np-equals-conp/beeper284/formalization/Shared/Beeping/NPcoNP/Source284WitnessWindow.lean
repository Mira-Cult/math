import Shared.Beeping.NPcoNP.Source284RawParse
import Shared.Beeping.NPcoNP.Source284Witness

/-! A finite, length-delimited witness representation for the 284 source's
natural-number certificate tape. The encoder and decoder are executable
list/natural data. Search theorems are parameterized by a Boolean relation;
they make no claim that an arbitrary parameter is computable. This file does
not implement a source transition table, prove polynomial runtime, or
establish candidate coverage. -/

namespace Shared.Beeping.NPcoNP.Source284WitnessWindow

open Shared.Codes.BitNumeralCompare (value)
open Shared.Codes.BinaryAdditionCanonical (Canonical canonical_value_bits)
open Shared.Beeping.NPcoNP.Source284Parser (frameBits)
open Shared.Beeping.NPcoNP.Source284RawParse (payload)

/-- Two bits per payload bit, a zero terminator, and a high sentinel. -/
def width (limit : Nat) : Nat := 2 * limit + 2

/-- The sentinel preserves even trailing zero payload bits in a canonical
natural representation. -/
def encode (witness : List Bool) : Nat := value (frameBits witness [true])

/-- Only the fixed low `width limit` bits are interpreted. A decoded witness
longer than the original bound is rejected explicitly. Higher natural-number
bits are aliases and are not claimed to be rejected. -/
def decode (limit certificate : Nat) : Option (List Bool) :=
  let w := payload (certificate % 2 ^ width limit).bits
  if w.length ≤ limit then some w else none

theorem frame_ne_nil (w : List Bool) : frameBits w [true] ≠ [] := by
  cases w <;> simp [frameBits]

theorem canonical_frame (w : List Bool) : Canonical (frameBits w [true]) := by
  induction w with
  | nil =>
    exact Canonical.cons false [true]
      (Canonical.cons true [] Canonical.nil (by simp)) (by simp)
  | cons b bs ih =>
    change Canonical (true :: b :: frameBits bs [true])
    apply Canonical.cons true
    · apply Canonical.cons b (frameBits bs [true]) ih
      intro h
      exact False.elim (frame_ne_nil bs h)
    · simp

theorem bits_encode (w : List Bool) : (encode w).bits = frameBits w [true] :=
  canonical_value_bits (canonical_frame w)

theorem payload_frame (w : List Bool) : payload (frameBits w [true]) = w := by
  induction w with
  | nil => rfl
  | cons b bs ih => simp [frameBits, payload, ih]

theorem frame_length (w : List Bool) : (frameBits w [true]).length = 2 * w.length + 2 := by
  induction w with
  | nil => rfl
  | cons b bs ih => simp [frameBits, ih] <;> omega

/-- Every witness within the old cutoff fits in the fixed certificate
window. -/
theorem encode_lt (limit : Nat) (w : List Bool) (hw : w.length ≤ limit) :
    encode w < 2 ^ width limit := by
  have h := Shared.Beeping.NPcoNP.Source284Witness.value_lt_pow_length (frameBits w [true])
  have he : (frameBits w [true]).length ≤ width limit := by
    rw [frame_length]
    simp only [width]
    omega
  exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) he)

/-- Every bounded list, including one with trailing false bits, round-trips. -/
theorem decode_encode (limit : Nat) (w : List Bool) (hw : w.length ≤ limit) :
    decode limit (encode w) = some w := by
  simp only [decode, Nat.mod_eq_of_lt (encode_lt limit w hw), bits_encode,
    payload_frame, hw, ↓reduceIte]

/-- A successfully decoded witness always meets the original list cutoff. -/
theorem decode_length (limit certificate : Nat) (w : List Bool)
    (h : decode limit certificate = some w) : w.length ≤ limit := by
  unfold decode at h
  dsimp only at h
  split_ifs at h with hb
  · cases h; exact hb

/-- The decoder depends only on the fixed low-bit window. -/
theorem decode_mod (limit certificate : Nat) :
    decode limit (certificate % 2 ^ width limit) = decode limit certificate := by
  simp [decode]

/-- A Boolean relation on decoded, cutoff-checked list witnesses. -/
def check (limit : Nat) (predicate : List Bool → Bool) (certificate : Nat) : Bool :=
  match decode limit certificate with
  | none => false
  | some w => predicate w

theorem check_mod (limit : Nat) (predicate : List Bool → Bool) (certificate : Nat) :
    check limit predicate (certificate % 2 ^ width limit) = check limit predicate certificate := by
  simp [check, decode_mod]

/-- The bounded numeric search represents precisely the original bounded
finite-list existential relation. -/
theorem bounded_search_iff (limit : Nat) (predicate : List Bool → Bool) :
    (∃ c, c < 2 ^ width limit ∧ check limit predicate c = true) ↔
      ∃ w, w.length ≤ limit ∧ predicate w = true := by
  constructor
  · rintro ⟨c, _, hc⟩
    cases h : decode limit c with
    | none => simp [check, h] at hc
    | some w =>
      exact ⟨w, decode_length limit c w h, by simpa [check, h] using hc⟩
  · rintro ⟨w, hw, hp⟩
    exact ⟨encode w, encode_lt limit w hw, by simpa [check, decode_encode limit w hw] using hp⟩

/-- Searching arbitrary natural numbers adds no accepting result: every
accepted alias has a representative in the fixed low-bit window. -/
theorem unbounded_search_iff (limit : Nat) (predicate : List Bool → Bool) :
    (∃ c, check limit predicate c = true) ↔
      ∃ w, w.length ≤ limit ∧ predicate w = true := by
  rw [← bounded_search_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c % 2 ^ width limit, Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
    simpa [check_mod] using hc
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc⟩

/-- Any finite certificate range covering the window has exactly the
original bounded-list existential behavior, despite accepting high-bit
aliases of valid encoded witnesses. -/
theorem oversupplied_search_iff (limit bound : Nat) (predicate : List Bool → Bool)
    (hbound : 2 ^ width limit ≤ bound) :
    (∃ c, c < bound ∧ check limit predicate c = true) ↔
      ∃ w, w.length ≤ limit ∧ predicate w = true := by
  rw [← bounded_search_iff]
  constructor
  · rintro ⟨c, _, hc⟩
    refine ⟨c % 2 ^ width limit, Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
    simpa [check_mod] using hc
  · rintro ⟨c, hc, hp⟩
    exact ⟨c, lt_of_lt_of_le hc hbound, hp⟩

/-- In particular, a source-style search through `2^clock` numeric
certificates adds no witnesses when the clock covers the encoded window. -/
theorem clock_search_iff (limit clock : Nat) (predicate : List Bool → Bool)
    (hclock : width limit ≤ clock) :
    (∃ c, c < 2 ^ clock ∧ check limit predicate c = true) ↔
      ∃ w, w.length ≤ limit ∧ predicate w = true :=
  oversupplied_search_iff limit (2 ^ clock) predicate
    (Nat.pow_le_pow_right (by decide) hclock)

example : decode 1 (encode [false]) = some [false] := by decide
example : decode 1 (encode []) = some [] := by decide
example : encode [false] ≠ encode [] := by decide

end Shared.Beeping.NPcoNP.Source284WitnessWindow
