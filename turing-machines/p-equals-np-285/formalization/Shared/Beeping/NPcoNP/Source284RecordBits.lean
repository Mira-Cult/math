import Shared.Beeping.NPcoNP.Source284Relative
import Shared.Codes.BitNumeralCompare

/-! Bit-list reading of the 284 source's unary records. Lists are little
endian; a missing bit is zero, just as in the natural-number evaluator.
This module proves extensional equivalence, not a runtime cost bound. -/

namespace Shared.Beeping.NPcoNP.Source284RecordBits

open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Codes.BitNumeralCompare (value)

/-- Consume one unary record, supplying a zero terminator at end of list. -/
def readBits : List Bool → Nat × List Bool
  | [] => (0, [])
  | false :: bs => (0, bs)
  | true :: bs => let r := readBits bs; (r.1 + 1, r.2)

/-- Skip a fixed number of records; the empty list stays empty. -/
def dropBits : List Bool → Nat → List Bool
  | bs, 0 => bs
  | bs, k + 1 => dropBits (readBits bs).2 k

/-- Record lookup on finite little-endian bits with a virtual zero tail. -/
def recordBits (bs : List Bool) (ordinal : Nat) : Nat :=
  (readBits (dropBits bs ordinal)).1

theorem readBits_correct (bs : List Bool) :
    readRecord (value bs) = ((readBits bs).1, value (readBits bs).2) := by
  induction bs with
  | nil => simp [value, readBits]
  | cons bit bs ih =>
    cases bit with
    | false =>
      have hm : value (false :: bs) % 2 = 0 := by simp [value]
      rw [readRecord_even _ hm]
      simp [value, readBits]
    | true =>
      have hm : value (true :: bs) % 2 = 1 := by simp [value]
      have hd : value (true :: bs) / 2 = value bs := by simp [value]; omega
      rw [readRecord_odd _ hm]
      rw [hd, ih]
      simp [readBits]

theorem dropBits_correct (bs : List Bool) (ordinal : Nat) :
    dropRecords (value bs) ordinal = value (dropBits bs ordinal) := by
  induction ordinal generalizing bs with
  | zero => rfl
  | succ k ih =>
    have h := congrArg Prod.snd (readBits_correct bs)
    simp only [Prod.snd] at h
    simp only [dropRecords, dropBits]
    rw [h, ih]

theorem recordBits_correct (bs : List Bool) (ordinal : Nat) :
    record (value bs) ordinal = recordBits bs ordinal := by
  unfold record recordBits
  rw [dropBits_correct]
  have h := congrArg Prod.fst (readBits_correct (dropBits bs ordinal))
  simpa using h

theorem recordBits_encodeNat (n ordinal : Nat) :
    recordBits (Computability.encodeNat n) ordinal = record n ordinal := by
  rw [← recordBits_correct, Shared.Codes.BitNumeralCompare.value_encodeNat]

end Shared.Beeping.NPcoNP.Source284RecordBits
