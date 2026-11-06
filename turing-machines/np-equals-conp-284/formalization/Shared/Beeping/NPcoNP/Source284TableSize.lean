import Shared.Beeping.NPcoNP.Source284TableRun
import Shared.Beeping.NPcoNP.Source284RecordSize

/-! A bit-size bound for the 284 source encoding of a closed finite relative
table. The table is still an arbitrary Lean function: this result does not
construct an effective serializer or establish its running time. The high
tail is one, whose extra later record is accounted for by the existing table
simulation only while the closed control remains in range. -/

namespace Shared.Beeping.NPcoNP.Source284TableSize

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284Relative

theorem bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> decide

/-- A row of a closed n-state table has a unary record value linear in n. -/
theorem rowCode_le (n : Nat) (table : Nat → Bool → Row)
    (closed : Closed n table) (q : Nat) (hq : q < n) (read : Bool) :
    rowCode (table q read) ≤ 8*n+7 := by
  have hw := bit_le_one (table q read).write
  have ht := bit_le_one (table q read).turn
  cases hn : (table q read).next with
  | none => simp only [rowCode, hn, nextState] at *; omega
  | some q' =>
    have hq' := closed q hq read q' hn
    simp only [rowCode, hn, nextState, active] at *
    omega

/-- Every encoded row is linear in the logical state count. -/
theorem records_bounded (n : Nat) (table : Nat → Bool → Row)
    (closed : Closed n table) :
    ∀ v ∈ records n table, v ≤ 8*n+7 := by
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  have hi : i.val / 2 < n := by have h := i.isLt; omega
  exact rowCode_le n table closed _ hi _

/-- The numerical source description uses at most quadratic many bits in
the number of states. This is a size result, not a running-time result. -/
theorem encode_size_bound (n : Nat) (table : Nat → Bool → Row)
    (closed : Closed n table) :
    Nat.size (encode n table 1) ≤ 1 + 2*n*(8*n+8) := by
  have h := size_sentinel_le (records n table) (8*n+7)
    (records_bounded n table closed)
  simpa [encode, records, Nat.add_assoc] using h

/-- Prepending the same unary record is monotone in the higher-bit tail. -/
theorem encodeRecord_mono (value : Nat) {a b : Nat} (h : a ≤ b) :
    encodeRecord value a ≤ encodeRecord value b := by
  induction value with
  | zero => simp only [encodeRecord]; omega
  | succ value ih => simp only [encodeRecord]; omega

theorem encodeRecords_mono (values : List Nat) {a b : Nat} (h : a ≤ b) :
    encodeRecords values a ≤ encodeRecords values b := by
  induction values with
  | nil => simpa [encodeRecords] using h
  | cons value values ih =>
    simp only [encodeRecords]
    exact encodeRecord_mono value ih

/-- The same quadratic bound applies to the zero-tail table encoding used
by the finite-table frame construction. -/
theorem encode_zero_size_bound (n : Nat) (table : Nat → Bool → Row)
    (closed : Closed n table) :
    Nat.size (encode n table 0) ≤ 1 + 2*n*(8*n+8) := by
  have hle : encode n table 0 ≤ encode n table 1 :=
    encodeRecords_mono (records n table) (by decide)
  exact (Nat.size_le_size hle).trans (encode_size_bound n table closed)

end Shared.Beeping.NPcoNP.Source284TableSize
