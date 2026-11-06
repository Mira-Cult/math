import Shared.Beeping.NPcoNP.Source284RecordEncoding
import Shared.Codes.BitNumeralCompare

/-! Bit-length accounting for the actual unary-record serialization used by
  the 284 source interpreter. The high sentinel is part of the finite code;
  no arithmetic operation here is assigned unit time. -/

namespace Shared.Beeping.NPcoNP.Source284Relative

/-- Number of low bits occupied by a sequence of unary records. -/
def recordBits (values : List Nat) : Nat :=
  (values.map (fun v => v + 1)).sum

/-- A nonzero tail survives prepending any finite number of records. -/
theorem encodeRecord_ne_zero (v tail : Nat) (ht : tail ≠ 0) :
    encodeRecord v tail ≠ 0 := by
  have h := encodeRecord_ge_tail v tail
  omega

/-- The unary word `1^v 0` occupies exactly `v+1` bits before a nonzero tail. -/
theorem size_encodeRecord (v tail : Nat) (ht : tail ≠ 0) :
    Nat.size (encodeRecord v tail) = Nat.size tail + v + 1 := by
  induction v with
  | zero =>
    have h : Nat.bit false tail ≠ 0 := by simp [ht]
    simpa [encodeRecord, Nat.bit_false] using (Nat.size_bit h)
  | succ v ih =>
    have h : Nat.bit true (encodeRecord v tail) ≠ 0 := by simp
    have hs := Nat.size_bit h
    simp only [Nat.bit_true] at hs
    simp only [encodeRecord]
    rw [hs, ih]
    omega

/-- Exact bit length of an entire unary-record prefix followed by a nonzero
sentinel/tail. This is a serialization-size theorem, not a runtime bound. -/
theorem size_encodeRecords (values : List Nat) (tail : Nat) (ht : tail ≠ 0) :
    Nat.size (encodeRecords values tail) = Nat.size tail + recordBits values := by
  induction values with
  | nil => simp [encodeRecords, recordBits]
  | cons value values ih =>
    have ht' : encodeRecords values tail ≠ 0 := by
      have h := encodeRecords_ge_tail values tail
      omega
    rw [encodeRecords, size_encodeRecord value _ ht', ih]
    simp [recordBits]
    omega

/-- With high tail 1, the encoding has exactly one additional bit beyond the
unary record payload. The tail itself supplies a later value-1 record; this
size theorem does not assert that a program cannot read that record. -/
theorem size_sentinel_encoding (values : List Nat) :
    Nat.size (encodeRecords values 1) = 1 + recordBits values := by
  simpa using size_encodeRecords values 1 (by decide)

/-- A uniform bound on record values yields a quadratic bit bound when the
record count and values are themselves bounded by the source table size. -/
theorem recordBits_le (values : List Nat) (bound : Nat)
    (h : ∀ v ∈ values, v ≤ bound) :
    recordBits values ≤ values.length * (bound + 1) := by
  induction values with
  | nil => simp [recordBits]
  | cons v vs ih =>
    have hv : v ≤ bound := h v (by simp)
    have hs : ∀ x ∈ vs, x ≤ bound := by
      intro x hx
      exact h x (by simp [hx])
    simp only [recordBits, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul] at *
    have ht := ih hs
    omega

theorem size_sentinel_le (values : List Nat) (bound : Nat)
    (h : ∀ v ∈ values, v ≤ bound) :
    Nat.size (encodeRecords values 1) ≤ 1 + values.length * (bound + 1) := by
  rw [size_sentinel_encoding]
  exact Nat.add_le_add_left (recordBits_le values bound h) 1

end Shared.Beeping.NPcoNP.Source284Relative
