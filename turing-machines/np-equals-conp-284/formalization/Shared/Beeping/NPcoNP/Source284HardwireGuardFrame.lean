import Shared.Beeping.NPcoNP.Source284HardwireGuardCode
import Shared.Beeping.NPcoNP.Source284ExplicitFrame

/-! A concrete finite-list guard and loader, serialized as the literal raw
bit list consumed by the source reference. The frame counts the full list,
including any high zero padding. No SAT reduction, complete cost theorem, or
physical-machine binding is asserted here. -/
namespace Shared.Beeping.NPcoNP.Source284HardwireGuardFrame

open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Codes.BitNumeralCompare (value)

/-- The actual serializer output; no normalization to `Nat.bits` is used. -/
def code (bits cutoff : List Bool) (original : EncRows) : List Bool :=
  let rs := decodeRows (Source284HardwireGuardRows.rows bits cutoff original)
  Source284TableRowsTM2.serializeRows (records rs.length (Source284ListTables.table rs))

/-- The raw source word, with a padding schedule charged for its exact length. -/
def framedInput (bits cutoff : List Bool) (original : EncRows) : List Bool :=
  Source284LinearPaddingTM2.frame (code bits cutoff original,bits,cutoff)

/-- For a nonempty, closed original list table, the independently serialized
finite guard and loader expose exactly the original cutoff-bounded acceptance
on its supplied input and all certificates below the original cutoff. -/
theorem reference_exact (bits cutoff : List Bool) (original : EncRows)
    (hn : 0 < original.length)
    (hclosed : Closed original.length (Source284ListTables.table (decodeRows original))) :
    reference (value (framedInput bits cutoff original)) = true ↔
      ∃ certificate, certificate < 2^cutoff.length ∧
        (run (Source284ListTables.table (decodeRows original))
          ⟨certificate,value bits,some 0⟩ cutoff.length).state.isNone = true := by
  unfold framedInput code
  dsimp only
  rw [Source284HardwireGuardCode.records_eq bits cutoff original]
  simpa only [Source284HardwireClock.states, Source284HardwireClock.guardedTable] using
    Source284ExplicitFrame.reference_guarded_serialized bits cutoff
      (Source284ListTables.table (decodeRows original)) original.length hn hclosed

end Shared.Beeping.NPcoNP.Source284HardwireGuardFrame
