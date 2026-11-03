import Shared.PNP.Record285.NumericBinding

/-! Reduction of the literal quotient obligation to the numeric certificate
and the concrete text-to-numeric parsing equalities. -/
namespace Shared.PNP.Record285.NumericLink
open Shared.Beeping.Machines
open Shared.PNP.Record285.Quotient
open Shared.PNP.Record285.NumericBinding

set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem literal_correct_of_parsed (sourceRows targetRows : List RawRow)
    (hsparse : Companion.parse = some sourceRows)
    (hsdata : sourceRows.map companionData = NumericTables.sourceData.toList)
    (htparse : Record285.parse = some targetRows)
    (htdata : targetRows.map markedData = NumericTables.targetData.toList)
    (hnum : check (NumericTables.source.entering Companion.beepState)
      NumericTables.target Companion.quotientMap = true) :
    Correct (Companion.machine.entering Companion.beepState) Record285.machine
      Companion.quotientMap := by
  have hc := check_sound _ _ _ hnum
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · intro q b
    rw [target_row_of_parsed targetRows htparse htdata]
    rw [hc.row]
    simp only [Machine.entering, Machine.withFlags, Table.row_withFlags,
      Flags.entering, Flags.at_ofFn]
    rw [source_row_of_parsed sourceRows hsparse hsdata]

/-- The two parsed row equalities are the remaining literal-data obligations. -/
theorem literal_check_of_parsed (sourceRows targetRows : List RawRow)
    (hsparse : Companion.parse = some sourceRows)
    (hsdata : sourceRows.map companionData = NumericTables.sourceData.toList)
    (htparse : Record285.parse = some targetRows)
    (htdata : targetRows.map markedData = NumericTables.targetData.toList)
    (hnum : check (NumericTables.source.entering Companion.beepState)
      NumericTables.target Companion.quotientMap = true) :
    check (Companion.machine.entering Companion.beepState) Record285.machine
      Companion.quotientMap = true :=
  check_complete _ _ _ (literal_correct_of_parsed sourceRows targetRows hsparse hsdata htparse htdata hnum)

end Shared.PNP.Record285.NumericLink
