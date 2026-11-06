import Shared.Beeping.NPcoNP.Source284TableSize

/-! A concrete finite-data presentation of the source's relative tables.
The row list is executable input; an out-of-range lookup defaults to an
accepting row. The checked source simulation only uses in-range rows.
No polynomial runtime or connection to a binary absolute-direction table
is asserted in this module. -/
namespace Shared.Beeping.NPcoNP.Source284ListTables

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284Relative

abbrev Rows := List (Row × Row)

def fallback : Row := ⟨false, false, none⟩

/-- Total finite-data table; only in-range state indices are semantically used. -/
def table (rows : Rows) (q : Nat) (read : Bool) : Row :=
  let pair := (rows[q]?).getD (fallback, fallback)
  if read then pair.2 else pair.1

def rowValid (n : Nat) (r : Row) : Bool :=
  match r.next with
  | none => true
  | some q => decide (q < n)

/-- Every stored successor is either acceptance or an in-range state. -/
def valid (rows : Rows) : Bool :=
  rows.all fun pair => rowValid rows.length pair.1 && rowValid rows.length pair.2

def source (rows : Rows) : Nat := encode rows.length (table rows) 0

theorem table_in_range (rows : Rows) (q : Nat) (h : q < rows.length) (read : Bool) :
    table rows q read = if read then rows[q].2 else rows[q].1 := by
  simp [table, h]

theorem valid_closed (rows : Rows) (h : valid rows = true) : Closed rows.length (table rows) := by
  intro q hq read q' hn
  have hall : ∀ p ∈ rows, rowValid rows.length p.1 = true ∧ rowValid rows.length p.2 = true := by
    simpa [valid, List.all_eq_true, Bool.and_eq_true] using h
  have hr := hall rows[q] (List.getElem_mem hq)
  rw [table_in_range rows q hq read] at hn
  cases read with
  | false =>
    change rows[q].1.next = some q' at hn
    have hv := hr.1
    simp [rowValid, hn] at hv
    exact hv
  | true =>
    change rows[q].2.next = some q' at hn
    have hv := hr.2
    simp [rowValid, hn] at hv
    exact hv

/-- The finite list is compiled into the already-verified source record
encoding; correctness applies to every finite clock and certificate. -/
theorem bounded_acceptance (rows : Rows) (hne : 0 < rows.length)
    (hv : valid rows = true) (input certificate clock : Nat) :
    Source284Relative.accepts (source rows) input certificate clock =
      (Source284TableRun.run (table rows) ⟨certificate, input, some 0⟩ clock).state.isNone := by
  exact Source284TableRun.bounded_acceptance rows.length (table rows) 0 hne
    (valid_closed rows hv) input certificate clock

/-- The source numeral of a validated finite-data table has quadratic bit
length in the number of rows. This bound does not prove runtime. -/
theorem source_size (rows : Rows) (hv : valid rows = true) :
    Nat.size (source rows) ≤ 1 + 2*rows.length*(8*rows.length+8) := by
  exact Source284TableSize.encode_zero_size_bound rows.length (table rows) (valid_closed rows hv)

example : valid [] = true := rfl
example : valid [(fallback, fallback)] = true := rfl
example : valid [(⟨false, false, some 1⟩, fallback)] = false := by decide

end Shared.Beeping.NPcoNP.Source284ListTables
