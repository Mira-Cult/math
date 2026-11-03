import Shared.Beeping.NPcoNP.Source284Relative

/-! Finite unary record encoding for the 284-state producer's source
interpreter. The arbitrary high tail permits padding a description without
changing its prescribed initial records. This does not by itself establish
that a running program stays within those records or that an encoding has
polynomial cost. -/

namespace Shared.Beeping.NPcoNP.Source284Relative

/-- Encode a unary `1^value 0` record before a high-order tail. -/
def encodeRecord : Nat → Nat → Nat
  | 0, tail => 2 * tail
  | value + 1, tail => 2 * encodeRecord value tail + 1

/-- Encode records from low to high bits, followed by an arbitrary tail. -/
def encodeRecords : List Nat → Nat → Nat
  | [], tail => tail
  | value :: values, tail => encodeRecord value (encodeRecords values tail)

theorem readRecord_encodeRecord (value tail : Nat) :
    readRecord (encodeRecord value tail) = (value, tail) := by
  induction value with
  | zero =>
    simp only [encodeRecord]
    rw [readRecord_even _ (by omega)]
    congr 1 <;> omega
  | succ value ih =>
    simp only [encodeRecord]
    rw [readRecord_odd _ (by omega)]
    have h : (2 * encodeRecord value tail + 1) / 2 = encodeRecord value tail := by omega
    rw [h, ih]

theorem encodeRecord_ge_tail (value tail : Nat) : tail ≤ encodeRecord value tail := by
  induction value with
  | zero => simp only [encodeRecord]; omega
  | succ value ih => simp only [encodeRecord]; omega

theorem encodeRecords_ge_tail (values : List Nat) (tail : Nat) :
    tail ≤ encodeRecords values tail := by
  induction values with
  | nil => simp [encodeRecords]
  | cons value values ih =>
    exact le_trans ih (encodeRecord_ge_tail value (encodeRecords values tail))

theorem record_encodeRecords (values : List Nat) (tail n : Nat)
    (h : n < values.length) :
    record (encodeRecords values tail) n = values[n] := by
  induction values generalizing n with
  | nil => simp at h
  | cons value values ih =>
    cases n with
    | zero => simp [record, dropRecords, encodeRecords, readRecord_encodeRecord]
    | succ n =>
      have hn : n < values.length := by simpa using h
      simpa [record, dropRecords, encodeRecords, readRecord_encodeRecord] using ih n hn

/-- Every finite record prefix occurs in descriptions above any given bound. -/
theorem records_unbounded (values : List Nat) (bound : Nat) :
    ∃ description > bound, ∀ n (h : n < values.length),
      record description n = values[n] := by
  refine ⟨encodeRecords values (bound + 1), ?_, ?_⟩
  · have := encodeRecords_ge_tail values (bound + 1)
    omega
  · intro n h
    exact record_encodeRecords values (bound + 1) n h

end Shared.Beeping.NPcoNP.Source284Relative
