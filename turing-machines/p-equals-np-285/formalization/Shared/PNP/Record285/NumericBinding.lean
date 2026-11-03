import Shared.PNP.Record285.NumericTables
import Shared.PNP.Record285.Companion

/-! Verified bridge from row-by-row parsed text data to generated numeric
rows. The concrete equalities between parsed data and arrays remain open. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace Shared.PNP.Record285.NumericBinding
open Shared.Beeping.Machines
open Shared.PNP.Record285.NumericTables

def markedData (r : RawRow) : DataRow :=
  (r.write == 1, match r.move with | .left => false | .right => true,
    r.next, r.event == 1)

def companionData (r : RawRow) : DataRow :=
  (r.write == 1, match r.move with | .left => false | .right => true,
    r.next, false)

@[simp] theorem marked_default : markedData Record285.defaultRow = (false,false,0,false) := rfl
@[simp] theorem companion_default : companionData Record285.defaultRow = (false,false,0,false) := rfl

theorem numericRow_marked (r : RawRow) :
    numericRow (by decide : 0 < 285) (markedData r) = Record285.physicalRow r := by
  cases r with
  | mk state read write move next event => cases move <;> rfl

theorem numericRow_companion (r : RawRow) :
    numericRow (by decide : 0 < 286) (companionData r) = Companion.physicalRow r := by
  cases r with
  | mk state read write move next event => cases move <;> rfl

/-- A row-list equality yields the corresponding exact row lookup, including
out-of-range defaults. -/
theorem lookup_of_mapped {α β : Type} (f : α → β) (fallback : α)
    (xs : List α) (data : Array β) (h : xs.map f = data.toList) (i : Nat) :
    (data[i]?).getD (f fallback) = f ((xs[i]?).getD fallback) := by
  rw [← Array.getElem?_toList, ← h, List.getElem?_map, Option.getD_map]

theorem target_row_of_parsed (parsed : List RawRow)
    (hparse : Record285.parse = some parsed) (hdata : parsed.map markedData = targetData.toList)
    (q : Fin 285) (read : Bool) :
    Record285.machine.table.row q read = NumericTables.target.table.row q read := by
  have lookup := lookup_of_mapped markedData Record285.defaultRow parsed targetData hdata
  have hrows : Record285.rows = parsed := by simp [Record285.rows, hparse]
  cases read with
  | false =>
    simp only [Record285.machine, Record285.table, Table.row, Bool.false_eq_true, if_false,
      Fin.getElem_fin, Vector.getElem_ofFn, NumericTables.target, numericTable, Record285.rowAt, hrows]
    rw [← marked_default, lookup, numericRow_marked]
  | true =>
    simp only [Record285.machine, Record285.table, Table.row, if_true,
      Fin.getElem_fin, Vector.getElem_ofFn, NumericTables.target, numericTable, Record285.rowAt, hrows]
    rw [← marked_default, lookup, numericRow_marked]

theorem source_row_of_parsed (parsed : List RawRow)
    (hparse : Companion.parse = some parsed) (hdata : parsed.map companionData = sourceData.toList)
    (q : Fin 286) (read : Bool) :
    Companion.machine.table.row q read = NumericTables.source.table.row q read := by
  have lookup := lookup_of_mapped companionData Record285.defaultRow parsed sourceData hdata
  have hrows : Companion.rows = parsed := by simp [Companion.rows, hparse]
  cases read with
  | false =>
    simp only [Companion.machine, Companion.table, Table.row, Bool.false_eq_true, if_false,
      Fin.getElem_fin, Vector.getElem_ofFn, NumericTables.source, numericTable, Companion.rowAt, hrows]
    rw [← companion_default, lookup, numericRow_companion]
  | true =>
    simp only [Companion.machine, Companion.table, Table.row, if_true,
      Fin.getElem_fin, Vector.getElem_ofFn, NumericTables.source, numericTable, Companion.rowAt, hrows]
    rw [← companion_default, lookup, numericRow_companion]

end Shared.PNP.Record285.NumericBinding
