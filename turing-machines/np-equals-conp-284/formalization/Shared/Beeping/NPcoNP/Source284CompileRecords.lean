import Shared.Beeping.NPcoNP.Source284RecordEncoding
import Shared.Codes.FinitePrograms

/-! Constructive source-record encoding for a finite binary table. Positive
source states use two orientations per table state and disjoint read rows.
The reserved state at `p.length` is a nonaccepting sink. This module proves
record lookup and bit-field identities only, not whole-run correctness or a
polynomial bit-cost bound. Continuing rows are not range-checked here: an
out-of-range destination can reach the source's virtual-zero records and
accept. A later simulation must require valid continuation destinations or
prove an explicit repair; invalid programs are not covered. -/
namespace Shared.Beeping.NPcoNP.Source284CompileRecords

open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Codes.FinitePrograms

def bit (b : Bool) : Nat := if b then 1 else 0

def codeState (q : Nat) (rev : Bool) : Nat := 4*q + 2*bit rev + 1

def recordIndex (q : Nat) (rev read : Bool) : Nat := 4*q + 2*bit rev + bit read

def rejectState (size : Nat) : Nat := codeState size false

/-- Source records store write, relative turn, and destination in base four.
FinitePrograms row direction is true for right and false for left. -/
def pack (write turn : Bool) (next : Nat) : Nat := bit write + 2*bit turn + 4*next

def encodedRow (size : Nat) (rev : Bool) (row : Row) : Nat :=
  let leftward := !row.2.1
  let next := if row.2.2.2 = 0 then codeState row.2.2.1 leftward
    else if row.2.2.2 = 2 then 0 else rejectState size
  pack row.1 (xor rev leftward) next

/-- Four records for every physical control state; a final block is reserved
for a rejection sink. The sink writes the current symbol, moves physically
right, and remains in the sink with forward orientation. -/
def recordAt (p : Program) (i : Nat) : Nat :=
  let q := i / 4
  let rev := (i / 2) % 2 = 1
  let read := i % 2 = 1
  if h : q < p.length then
    let rows := p[q]
    encodedRow p.length (decide rev) (if read then rows.2 else rows.1)
  else
    pack (decide read) (decide rev) (rejectState p.length)

def records (p : Program) : List Nat :=
  List.ofFn (fun i : Fin (4*(p.length+1)) => recordAt p i.val)

def compile (p : Program) : Nat := encodeRecords (records p) 1

@[simp] theorem bit_lt (b : Bool) : bit b < 2 := by cases b <;> decide
@[simp] theorem state_positive (q : Nat) (rev : Bool) : 0 < codeState q rev := by
  cases rev <;> simp [codeState, bit] <;> omega

theorem source_index (q : Nat) (rev read : Bool) :
    codeState q rev - 1 + bit read = recordIndex q rev read := by
  cases rev <;> cases read <;> simp [codeState, recordIndex, bit] <;> omega

theorem index_div_four (q : Nat) (rev read : Bool) :
    recordIndex q rev read / 4 = q := by
  cases rev <;> cases read <;> simp [recordIndex, bit] <;> omega

theorem index_rev (q : Nat) (rev read : Bool) :
    decide ((recordIndex q rev read / 2) % 2 = 1) = rev := by
  cases rev <;> cases read <;> simp [recordIndex, bit] <;> omega

theorem index_read (q : Nat) (rev read : Bool) :
    decide (recordIndex q rev read % 2 = 1) = read := by
  cases rev <;> cases read <;> simp [recordIndex, bit] <;> omega

theorem index_bound (p : Program) (q : Nat) (rev read : Bool) (h : q ≤ p.length) :
    recordIndex q rev read < (records p).length := by
  simp only [records, List.length_ofFn]
  cases rev <;> cases read <;> simp [recordIndex, bit] <;> omega

theorem recordAt_state (p : Program) (q : Nat) (rev read : Bool) (h : q < p.length) :
    recordAt p (recordIndex q rev read) =
      encodedRow p.length rev (if read then p[q].2 else p[q].1) := by
  simp only [recordAt, index_div_four, h, ↓reduceDIte]
  have hr := index_rev q rev read
  have hb := index_read q rev read
  cases rev <;> cases read <;> simp_all [bit]

theorem compiled_record (p : Program) (q : Nat) (rev read : Bool) (h : q < p.length) :
    record (compile p) (codeState q rev - 1 + bit read) =
      encodedRow p.length rev (if read then p[q].2 else p[q].1) := by
  rw [source_index]
  unfold compile
  rw [record_encodeRecords _ _ _ (index_bound p q rev read (by omega))]
  simpa only [records, List.getElem_ofFn] using recordAt_state p q rev read h

theorem recordAt_sink (p : Program) (rev read : Bool) :
    recordAt p (recordIndex p.length rev read) =
      pack read rev (rejectState p.length) := by
  simp only [recordAt, index_div_four, lt_self_iff_false, ↓reduceDIte]
  have hr := index_rev p.length rev read
  have hb := index_read p.length rev read
  cases rev <;> cases read <;> simp_all [bit]

theorem compiled_sink (p : Program) (rev read : Bool) :
    record (compile p) (codeState p.length rev - 1 + bit read) =
      pack read rev (rejectState p.length) := by
  rw [source_index]
  unfold compile
  rw [record_encodeRecords _ _ _ (index_bound p p.length rev read le_rfl)]
  simpa only [records, List.getElem_ofFn] using recordAt_sink p rev read

@[simp] theorem pack_write (w t : Bool) (n : Nat) : pack w t n % 2 = bit w := by
  cases w <;> cases t <;> simp [pack, bit] <;> omega
@[simp] theorem pack_turn (w t : Bool) (n : Nat) : (pack w t n / 2) % 2 = bit t := by
  cases w <;> cases t <;> simp [pack, bit] <;> omega
@[simp] theorem pack_next (w t : Bool) (n : Nat) : pack w t n / 4 = n := by
  cases w <;> cases t <;> simp [pack, bit] <;> omega

end Shared.Beeping.NPcoNP.Source284CompileRecords
