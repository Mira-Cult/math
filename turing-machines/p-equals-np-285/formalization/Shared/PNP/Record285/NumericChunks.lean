import Shared.PNP.Record285.NumericTables
import Shared.PNP.Record285.Companion
namespace Shared.PNP.Record285.NumericChunks
open Shared.Beeping.Machines
open Shared.PNP.Record285
open Shared.PNP.Record285.Quotient

/-- Executable checks of all rows in a bounded interval of source states. -/
def rowsCheck (start count : Nat) : Bool :=
  (List.range' start count).all fun i =>
    if h : i < 286 then
      let q : Fin 286 := ⟨i,h⟩
      decide (NumericTables.target.table.row (Companion.quotientMap q) false =
        mappedRow Companion.quotientMap ((NumericTables.source.entering Companion.beepState).table.row q false)) &&
      decide (NumericTables.target.table.row (Companion.quotientMap q) true =
        mappedRow Companion.quotientMap ((NumericTables.source.entering Companion.beepState).table.row q true))
    else false

set_option maxRecDepth 8192
set_option maxHeartbeats 0
theorem chunk0 : rowsCheck 0 16 = true := by decide
theorem chunk1 : rowsCheck 16 16 = true := by decide
theorem chunk2 : rowsCheck 32 16 = true := by decide
theorem chunk3 : rowsCheck 48 16 = true := by decide
theorem chunk4 : rowsCheck 64 16 = true := by decide
theorem chunk5 : rowsCheck 80 16 = true := by decide
theorem chunk6 : rowsCheck 96 16 = true := by decide
theorem chunk7 : rowsCheck 112 16 = true := by decide
theorem chunk8 : rowsCheck 128 16 = true := by decide
theorem chunk9 : rowsCheck 144 16 = true := by decide
theorem chunk10 : rowsCheck 160 16 = true := by decide
theorem chunk11 : rowsCheck 176 16 = true := by decide
theorem chunk12 : rowsCheck 192 16 = true := by decide
theorem chunk13 : rowsCheck 208 16 = true := by decide
theorem chunk14 : rowsCheck 224 16 = true := by decide
theorem chunk15 : rowsCheck 240 16 = true := by decide
theorem chunk16 : rowsCheck 256 16 = true := by decide
theorem chunk17 : rowsCheck 272 14 = true := by decide
end Shared.PNP.Record285.NumericChunks
