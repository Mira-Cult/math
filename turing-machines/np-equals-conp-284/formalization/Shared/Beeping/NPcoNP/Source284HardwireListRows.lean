import Shared.Beeping.NPcoNP.Source284HardwireTable
import Shared.Beeping.NPcoNP.Source284ListTables

/-! Materialize the paid fixed-input loader over an explicit list of
relative-direction rows. The supplied list can itself be a countdown-guarded
table, but this module does not construct or validate such a guard. No
running-time or size bound beyond the exact row count is claimed. -/
namespace Shared.Beeping.NPcoNP.Source284HardwireListRows

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284ListTables

/-- The entire paid loader, followed by the relocated input table. -/
def rows (bits : List Bool) (original : Rows) : Rows :=
  List.ofFn fun q : Fin (offset bits + original.length) =>
    (Source284HardwireTable.table bits (Source284ListTables.table original) q.val false,
     Source284HardwireTable.table bits (Source284ListTables.table original) q.val true)

@[simp] theorem rows_length (bits : List Bool) (original : Rows) :
    (rows bits original).length = offset bits + original.length := by
  simp [rows]

/-- Every represented row is exactly the existing loader row, including the
original list's handling of invalid stored destinations. -/
theorem row_agreement (bits : List Bool) (original : Rows) (q : Nat)
    (h : q < offset bits + original.length) (read : Bool) :
    Source284ListTables.table (rows bits original) q read =
      Source284HardwireTable.table bits (Source284ListTables.table original) q read := by
  have h' : q < (rows bits original).length := by simpa using h
  rw [Source284ListTables.table_in_range _ _ h']
  cases read <;> simp [rows]

/-- Outside the materialized table, list lookup uses its explicit accepting
fallback. In particular this is not a claim that an arbitrary function table
has the same out-of-range behavior. -/
theorem out_of_range (bits : List Bool) (original : Rows) (q : Nat)
    (h : offset bits + original.length ≤ q) (read : Bool) :
    Source284ListTables.table (rows bits original) q read = fallback := by
  have hn : (rows bits original).length ≤ q := by simpa using h
  simp [Source284ListTables.table, List.getElem?_eq_none hn]

end Shared.Beeping.NPcoNP.Source284HardwireListRows
