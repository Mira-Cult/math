import Shared.Beeping.NPcoNP.Source284EncodedRecordListTM2
import Shared.Beeping.NPcoNP.Source284HardwireGuardRowsTM2
import Shared.Beeping.NPcoNP.Source284HardwireGuardCode
import Shared.Beeping.NPcoNP.Source284TableRowsTM2

/-! Executable literal record-word compiler for the guarded finite table.
The serializer clamps arbitrary row codes to a polynomial unary budget;
the guarded table is closed, so its rows fit and no clamp occurs. Numeric
agreement is stated explicitly; trailing delimiters need not equal `.bits`.
This module makes no claim about framing, SAT hardness or the physical table. -/
namespace Shared.Beeping.NPcoNP.Source284GuardedBitsTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284EncodedRecordList
open Shared.Beeping.NPcoNP.Source284EncodedRecordListTM2
open Shared.Beeping.NPcoNP.Source284TableRowsTM2
open Shared.Codes.BitNumeralCompare (value)

abbrev Input := List Bool × (List Bool × EncRows)

def bits (p : Input) : List Bool :=
  serializeRows (recordsList (Source284HardwireGuardRows.rows p.1 p.2.1 p.2.2))

theorem bits_isPolyTime : IsPolyTime bits := by
  let rs : Input → EncRows := fun p => Source284HardwireGuardRows.rows p.1 p.2.1 p.2.2
  have hr : IsPolyTime rs := Source284HardwireGuardRowsTM2.rows_isPolyTime
  have hc := TM2Compose.isPolyTime_comp rs recordsList hr recordsList_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p => recordsList (rs p)) serializeRows hc serializeRows_isPolyTime

/-- The explicit bounded word represents exactly the code of the closed
function table used by the established hardwire/countdown semantics. -/
theorem bits_value (xs cutoff : List Bool) (original : EncRows) :
    value (bits (xs,(cutoff,original))) =
      Shared.Beeping.NPcoNP.Source284TableEncode.encode
        (Source284HardwireClock.states xs original.length cutoff.length)
        (Source284HardwireClock.guardedTable xs (Source284ListTables.table (decodeRows original))
          original.length cutoff.length) 0 := by
  unfold bits
  rw [recordsList_eq, Source284HardwireGuardCode.records_eq]
  exact closed_table_correct _ _ (Source284HardwireClock.guarded_closed xs
    (Source284ListTables.table (decodeRows original)) original.length cutoff.length)

end Shared.Beeping.NPcoNP.Source284GuardedBitsTM2
