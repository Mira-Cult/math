import Shared.Beeping.NPcoNP.Source284HardwireIndexedList
import Shared.Beeping.NPcoNP.Source284GuardTableListTM2

/-! Semantic composition of the explicit countdown-table and hardwired-input
constructors. The cutoff is supplied in unary as a list; this module compares
finite table rows only and makes no machine-endpoint or overall runtime claim. -/
namespace Shared.Beeping.NPcoNP.Source284HardwireGuardRows

open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284HardwireTable

/-- Materialize a countdown guard, then prepend the paid input loader. -/
def rows (bits cutoff : List Bool) (original : EncRows) : EncRows :=
  Source284HardwireIndexedList.rows bits
    (Source284GuardTableListTM2.tableRows (cutoff, original))

@[simp] theorem rows_length (bits cutoff : List Bool) (original : EncRows) :
    (rows bits cutoff original).length = offset bits +
      Source284TableCountdown.allocated original.length cutoff.length := by
  simp [rows, Source284HardwireIndexedList.rows,
    Source284HardwireIndexedList.loaderPrefix_eq,
    Source284GuardTableListTM2.tableRows_length]

/-- On every allocated state and both symbols, the materialized table is the
existing hardwired countdown table. This statement includes invalid input
rows; it does not assume that the input table is closed. -/
theorem row_agreement (bits cutoff : List Bool) (original : EncRows)
    (q : Nat) (hq : q < offset bits +
      Source284TableCountdown.allocated original.length cutoff.length) (read : Bool) :
    Source284ListTables.table (decodeRows (rows bits cutoff original)) q read =
      Source284HardwireTable.table bits
        (Source284TableCountdown.table original.length cutoff.length
          (Source284ListTables.table (decodeRows original))) q read := by
  unfold rows
  rw [Source284HardwireIndexedList.decode_rows]
  have hb : q < offset bits +
      (decodeRows (Source284GuardTableListTM2.tableRows (cutoff, original))).length := by
    simpa [Source284GuardTableListTM2.tableRows_length] using hq
  rw [Source284HardwireListRows.row_agreement _ _ _ hb]
  unfold Source284HardwireTable.table
  split_ifs with hwrite hturn hback hlast
  · rfl
  · rfl
  · rfl
  · rfl
  · have hbase : offset bits ≤ q := by simp only [offset]; omega
    have hq0 : q - offset bits <
        Source284TableCountdown.allocated original.length cutoff.length := by omega
    rw [Source284GuardTableListTM2.tableRows_correct cutoff original _ hq0 read]

end Shared.Beeping.NPcoNP.Source284HardwireGuardRows
