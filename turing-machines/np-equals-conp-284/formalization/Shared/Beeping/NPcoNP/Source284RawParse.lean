import Shared.Beeping.NPcoNP.Source284Suffix

/-! A raw-bit-list front end for the pinned 284 source parser. The low bit
comes first; high zeroes are permitted, and a missing payload bit is a
virtual zero. This module proves extensional correctness only, not a
canonical polynomial-time implementation. -/

namespace Shared.Beeping.NPcoNP.Source284RawParse

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Parser

/-- Payloads in source order, up to the first zero marker. -/
def payload : List Bool → List Bool
  | [] => []
  | false :: _ => []
  | [true] => [false]
  | true :: b :: bs => b :: payload bs

/-- The marker stream drives the same accumulator transformation as the
numeric parser. A lone true marker reads its absent payload as zero. -/
theorem run_value (bits : List Bool) (n e : Nat) :
    run (value bits) n e = (n + (payload bits).length, payloadFold e (payload bits)) := by
  induction bits using List.twoStepInduction generalizing n e with
  | nil => simp [value, payload, run_even, payloadFold]
  | singleton b =>
    cases b with
    | false => simp [value, payload, run_even, payloadFold]
    | true =>
      rw [show value [true] = 1 by rfl, run_odd 1 n e (by decide)]
      simp [run_even, payload, payloadFold]
  | cons_cons a b bs ih _ =>
    cases a with
    | false =>
      have he : value (false :: b :: bs) % 2 = 0 := by simp [value]
      rw [run_even _ _ _ he]
      simp [payload, payloadFold]
    | true =>
      have ho : value (true :: b :: bs) % 2 = 1 := by simp [value]
      have hd : value (true :: b :: bs) / 4 = value bs := by
        cases b <;> simp [value] <;> omega
      have hb : (value (true :: b :: bs) / 2) % 2 = if b then 1 else 0 := by
        cases b <;> simp [value] <;> omega
      rw [run_odd _ _ _ ho, hd, hb, ih]
      simp [payload, payloadFold, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem parse_value (bits : List Bool) :
    parse (value bits) = ((payload bits).length, payloadFold 1 (payload bits)) := by
  simpa [parse] using run_value bits 0 1

/-- The high sentinel after the reversed payload is a faithful low-endian
bit representation of the exact source description. -/
theorem parse_description_bits (bits : List Bool) :
    description (value bits) = value ((payload bits).reverse ++ [true]) := by
  unfold description
  rw [parse_value, payloadFold_value, bitValue_append]
  simp [value, Nat.add_comm]

theorem parse_length (bits : List Bool) :
    Source284Parser.length (value bits) = (payload bits).length := by
  simp [Source284Parser.length, parse_value]

/-- The virtual final payload never makes the output longer than the raw
input: it only occurs when that input ends with the true marker. -/
theorem payload_length_le (bits : List Bool) : (payload bits).length ≤ bits.length := by
  induction bits using List.twoStepInduction with
  | nil => simp [payload]
  | singleton b => cases b <;> simp [payload]
  | cons_cons a b bs ih _ => cases a <;> simp [payload] at * <;> omega

end Shared.Beeping.NPcoNP.Source284RawParse
