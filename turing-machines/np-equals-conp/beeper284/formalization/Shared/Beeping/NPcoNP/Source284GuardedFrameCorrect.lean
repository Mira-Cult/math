import Shared.Beeping.NPcoNP.Source284GuardedFrameTM2
import Shared.Beeping.NPcoNP.Source284HardwireGuardFrame

/-! The polynomial constructor's output is the very same raw list used in the
finite-table reference theorem. No normalization to a numeral bit list is
performed; the entire serializer output contributes to the frame clock. -/
namespace Shared.Beeping.NPcoNP.Source284GuardedFrameCorrect

open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Codes.BitNumeralCompare (value)

/-- Equality of literal lists, not only equality of their numeric values. -/
theorem bits_eq_code (bits cutoff : List Bool) (original : EncRows) :
    Source284GuardedBitsTM2.bits (bits,(cutoff,original)) =
      Source284HardwireGuardFrame.code bits cutoff original := by
  unfold Source284GuardedBitsTM2.bits Source284HardwireGuardFrame.code
  rw [Source284EncodedRecordList.recordsList_eq]

/-- The paid constructor and the semantic reference frame use the same
literal bit list and hence the same length-dependent padding. -/
theorem frame_eq (bits cutoff : List Bool) (original : EncRows) :
    Source284GuardedFrameTM2.frame (bits,(cutoff,original)) =
      Source284HardwireGuardFrame.framedInput bits cutoff original := by
  simp only [Source284GuardedFrameTM2.frame, Source284HardwireGuardFrame.framedInput,
    bits_eq_code]

/-- The concrete polynomial frame constructor has the previously established
source-reference meaning for every nonempty, closed finite relative table.
This is a source-level theorem, not a physical-machine certification. -/
theorem reference_exact (bits cutoff : List Bool) (original : EncRows)
    (hn : 0 < original.length)
    (hclosed : Closed original.length (Source284ListTables.table (decodeRows original))) :
    reference (value (Source284GuardedFrameTM2.frame (bits,(cutoff,original)))) = true ↔
      ∃ certificate, certificate < 2^cutoff.length ∧
        (run (Source284ListTables.table (decodeRows original))
          ⟨certificate,value bits,some 0⟩ cutoff.length).state.isNone = true := by
  rw [frame_eq]
  exact Source284HardwireGuardFrame.reference_exact bits cutoff original hn hclosed

end Shared.Beeping.NPcoNP.Source284GuardedFrameCorrect
