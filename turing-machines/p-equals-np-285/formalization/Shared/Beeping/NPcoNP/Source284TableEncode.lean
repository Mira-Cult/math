import Shared.Beeping.NPcoNP.Source284RecordEncoding

/-! Encoding finite relative-direction transition tables in the source's
unary-record language. The source's lookup indices overlap on consecutive
state numbers; logical states are therefore represented by odd positive
numbers. State zero is the source's accepting state. This file provides no
runtime or complexity bound and does not relate a concrete table to a tape
machine. -/

namespace Shared.Beeping.NPcoNP.Source284TableEncode

open Shared.Beeping.NPcoNP.Source284Relative

/-- A relative write/turn transition. `none` denotes acceptance. -/
structure Row where
  write : Bool
  turn : Bool
  next : Option Nat
  deriving DecidableEq, Repr

def bit (b : Bool) : Nat := if b then 1 else 0

/-- Encode a logical state as an odd nonzero source state. -/
def active (q : Nat) : Nat := 2 * q + 1

def nextState : Option Nat → Nat
  | none => 0
  | some q => active q

def rowCode (r : Row) : Nat := bit r.write + 2 * bit r.turn + 4 * nextState r.next

theorem rowCode_write (r : Row) : rowCode r % 2 = bit r.write := by
  cases r with
  | mk w t n => cases w <;> cases t <;> simp [rowCode, bit] <;> omega

theorem rowCode_turn (r : Row) : (rowCode r / 2) % 2 = bit r.turn := by
  cases r with
  | mk w t n => cases w <;> cases t <;> simp [rowCode, bit] <;> omega

theorem rowCode_next (r : Row) : rowCode r / 4 = nextState r.next := by
  cases r with
  | mk w t n => cases w <;> cases t <;> simp [rowCode, bit] <;> omega

/-- The finite table is listed in the source lookup order: read zero then
read one for each logical state. The table is only observed for `q < n`. -/
def records (n : Nat) (table : Nat → Bool → Row) : List Nat :=
  List.ofFn (fun i : Fin (2*n) => rowCode (table (i.val / 2) (i.val % 2 = 1)))

def encode (n : Nat) (table : Nat → Bool → Row) (tail : Nat) : Nat :=
  encodeRecords (records n table) tail

theorem record_lookup (n : Nat) (table : Nat → Bool → Row) (tail q : Nat)
    (h : q < n) (read : Bool) :
    record (encode n table tail) (active q - 1 + bit read) =
      rowCode (table q read) := by
  have hindex : active q - 1 + bit read < (records n table).length := by
    cases read <;> simp [records, active, bit] <;> omega
  rw [encode, record_encodeRecords _ _ _ hindex]
  have h0 : (2 * q) / 2 = q := by omega
  have h1 : (2 * q + 1) / 2 = q := by omega
  cases read <;> simp [records, active, bit, h0, h1]

/-- The source step taken from a represented logical state is precisely the
table's relative write/turn step. The finite tape halves are arbitrary; the
resulting state is zero for acceptance and otherwise the next odd state. -/
theorem step_lookup (n : Nat) (table : Nat → Bool → Row) (tail q left right : Nat)
    (h : q < n) :
    let read := right.testBit 0
    let r := table q read
    step (encode n table tail) ⟨left, right, active q⟩ =
      if r.turn then ⟨2 * (right / 2) + bit r.write, left, nextState r.next⟩
      else ⟨2 * left + bit r.write, right / 2, nextState r.next⟩ := by
  have hbit : bit (right.testBit 0) = right % 2 := by
    rw [Nat.testBit_zero]
    have hb := Nat.mod_lt right (by decide : 0 < 2)
    by_cases hh : right % 2 = 1
    · simp [bit, hh]
    · have hz : right % 2 = 0 := by omega
      simp [bit, hz]
  have hrow := record_lookup n table tail q h (right.testBit 0)
  rw [hbit] at hrow
  have hrow' : record (encode n table tail) (2 * q + right % 2) =
      rowCode (table q (right.testBit 0)) := by simpa [active] using hrow
  cases ht : (table q (right.testBit 0)).turn <;>
    simp [step, active, hrow', rowCode_write, rowCode_turn, rowCode_next, bit, ht]

end Shared.Beeping.NPcoNP.Source284TableEncode
