import Shared.PNP.Record285.NumericBinding
import Shared.PNP.Record285.PhysicalNumeric

/-! Exact rows for the five-state first bootstrap in the generated numeric
copy. The literal text binding remains an explicit separate premise. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace Shared.PNP.Record285.BootstrapRows
open Shared.Beeping.Machines
open Shared.PNP.Record285.NumericBinding

def A : Fin 285 := ⟨0, by decide⟩
def B : Fin 285 := ⟨2, by decide⟩
def C : Fin 285 := ⟨3, by decide⟩
def D : Fin 285 := ⟨4, by decide⟩
def E : Fin 285 := ⟨5, by decide⟩
def exit : Fin 285 := ⟨76, by decide⟩

/-- All bootstrap transitions, including the outgoing C/1 row and flags. -/
structure Rows (M : Machine 285) : Prop where
  A0 : M.table.row A false = ⟨true,.right,B,false⟩
  A1 : M.table.row A true = ⟨true,.left,C,false⟩
  B0 : M.table.row B false = ⟨false,.left,A,false⟩
  B1 : M.table.row B true = ⟨false,.left,D,false⟩
  C0 : M.table.row C false = ⟨true,.left,A,false⟩
  C1 : M.table.row C true = ⟨true,.right,exit,false⟩
  D0 : M.table.row D false = ⟨true,.left,B,false⟩
  D1 : M.table.row D true = ⟨true,.right,E,false⟩
  E0 : M.table.row E false = ⟨false,.right,D,false⟩
  E1 : M.table.row E true = ⟨false,.right,B,false⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
/-- The ten generated numeric rows are checked by kernel reduction. -/
theorem numeric_rows : Rows NumericTables.target := by
  constructor <;> decide

/-- The literal rows satisfy the same interface if their parsing and numeric
row-data equality are supplied. Neither hypothesis has yet been discharged. -/
theorem literal_rows_of_parsed (parsed : List RawRow)
    (hparse : Record285.parse = some parsed)
    (hdata : parsed.map markedData = NumericTables.targetData.toList) : Rows Record285.machine := by
  constructor <;> rw [target_row_of_parsed parsed hparse hdata]
  all_goals first | exact numeric_rows.A0 | exact numeric_rows.A1 | exact numeric_rows.B0 |
    exact numeric_rows.B1 | exact numeric_rows.C0 | exact numeric_rows.C1 |
    exact numeric_rows.D0 | exact numeric_rows.D1 | exact numeric_rows.E0 | exact numeric_rows.E1

end Shared.PNP.Record285.BootstrapRows
