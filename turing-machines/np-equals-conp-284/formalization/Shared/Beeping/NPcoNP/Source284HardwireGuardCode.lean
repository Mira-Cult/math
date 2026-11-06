import Shared.Beeping.NPcoNP.Source284HardwireGuardRows
import Shared.Beeping.NPcoNP.Source284HardwireClock

/-! The explicit guarded loader compiles to the same finite source program as
the existing function-table construction. This is a semantic equality only;
constructing its literal bit word and bounding time are separate obligations. -/
namespace Shared.Beeping.NPcoNP.Source284HardwireGuardCode

open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284HardwireClock
open Shared.Beeping.NPcoNP.Source284HardwireTable (offset)

/-- Every source record of the explicit finite-data construction agrees
with the record of the previously verified guarded function table. -/
theorem records_eq (bits cutoff : List Bool) (original : EncRows) :
    records (decodeRows (Source284HardwireGuardRows.rows bits cutoff original)).length
        (Source284ListTables.table (decodeRows (Source284HardwireGuardRows.rows bits cutoff original))) =
      records (states bits original.length cutoff.length)
        (guardedTable bits (Source284ListTables.table (decodeRows original))
          original.length cutoff.length) := by
  simp only [decodeRows_length, Source284HardwireGuardRows.rows_length]
  change List.ofFn _ = List.ofFn _
  apply congrArg List.ofFn
  funext i
  have hi : i.val / 2 < offset bits +
      Source284TableCountdown.allocated original.length cutoff.length := by omega
  have h := Source284HardwireGuardRows.row_agreement bits cutoff original
    (i.val / 2) hi (i.val % 2 = 1)
  simp only [states, guardedTable]
  rw [h]

/-- Zero-tail source numerals, hence the exact reference programs, agree. -/
theorem source_eq (bits cutoff : List Bool) (original : EncRows) :
    Source284ListTables.source (decodeRows (Source284HardwireGuardRows.rows bits cutoff original)) =
      encode (states bits original.length cutoff.length)
        (guardedTable bits (Source284ListTables.table (decodeRows original))
          original.length cutoff.length) 0 := by
  unfold Source284ListTables.source encode
  rw [records_eq bits cutoff original]

end Shared.Beeping.NPcoNP.Source284HardwireGuardCode
