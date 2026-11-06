import Shared.Beeping.NPcoNP.Source284RecordEncoding
import Shared.Codes.BitNumeralCompare

/-! Finite source-record representation of the source reference's sentinel.
The code is low-endian, and an explicit zero after it terminates every unary
record before the sentinel. This is a finite encoding identity, not a runtime
or source-to-physical-machine theorem. -/

namespace Shared.Beeping.NPcoNP.Source284SentinelRecords

open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Codes.BitNumeralCompare

/-- Prefix one bit to a nonempty, already terminated sequence of unary
records. The unreachable empty case stays empty. -/
def prependBit : Bool → List Nat → List Nat
  | false, values => 0 :: values
  | true, [] => []
  | true, value :: values => (value + 1) :: values

/-- Prefix low-endian bits to an existing nonempty record sequence. -/
def prependBits : List Bool → List Nat → List Nat
  | [], values => values
  | bit :: bits, values => prependBit bit (prependBits bits values)

theorem prependBit_nonempty (bit : Bool) (values : List Nat) (h : values ≠ []) :
    prependBit bit values ≠ [] := by
  cases bit <;> cases values <;> simp_all [prependBit]

theorem prependBits_nonempty (bits : List Bool) (values : List Nat) (h : values ≠ []) :
    prependBits bits values ≠ [] := by
  induction bits with
  | nil => exact h
  | cons bit bits ih => exact prependBit_nonempty bit _ ih

theorem encode_prependBit (bit : Bool) (values : List Nat) (h : values ≠ []) (tail : Nat) :
    encodeRecords (prependBit bit values) tail =
      2 * encodeRecords values tail + (if bit then 1 else 0) := by
  cases bit <;> cases values <;> simp_all [prependBit, encodeRecords, encodeRecord]

theorem encode_prependBits (bits : List Bool) (values : List Nat) (h : values ≠ []) (tail : Nat) :
    encodeRecords (prependBits bits values) tail =
      value bits + 2 ^ bits.length * encodeRecords values tail := by
  induction bits with
  | nil => simp [prependBits, value]
  | cons bit bits ih =>
    rw [prependBits, encode_prependBit bit _ (prependBits_nonempty bits values h) tail, ih]
    simp only [value, List.length_cons, pow_succ]
    ring

theorem encode_zeroRecords (n tail : Nat) :
    encodeRecords (List.replicate n 0) tail = 2 ^ n * tail := by
  induction n with
  | zero => simp [encodeRecords]
  | succ n ih =>
    simp only [List.replicate_succ, encodeRecords, encodeRecord, ih, pow_succ]
    ring

/-- Build the finite unary records for a program followed by `padding+1`
zero bits. The initial terminating zero is essential when the code itself
ends in one. -/
def records (code : List Bool) (padding : Nat) : List Nat :=
  prependBits code (List.replicate (padding+1) 0)

/-- Original code and the source's sentinel-extended code differ only in
what follows the same explicitly terminated finite record list. -/
theorem sentinel_representation (code : List Bool) (padding : Nat) :
    value code = encodeRecords (records code padding) 0 ∧
    2 ^ (code.length + (padding+1)) + value code =
      encodeRecords (records code padding) 1 := by
  have hn : List.replicate (padding+1) 0 ≠ ([] : List Nat) := by simp
  have h0 := encode_prependBits code (List.replicate (padding+1) 0) hn 0
  have h1 := encode_prependBits code (List.replicate (padding+1) 0) hn 1
  change value code = encodeRecords (prependBits code (List.replicate (padding+1) 0)) 0 ∧
    2 ^ (code.length + (padding+1)) + value code =
      encodeRecords (prependBits code (List.replicate (padding+1) 0)) 1
  constructor
  · rw [h0, encode_zeroRecords]
    simp
  · rw [h1, encode_zeroRecords, pow_add]
    ring

end Shared.Beeping.NPcoNP.Source284SentinelRecords
