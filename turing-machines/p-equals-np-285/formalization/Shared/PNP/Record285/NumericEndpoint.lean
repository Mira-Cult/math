import Shared.PNP.Record285.NumericCertificate
import Shared.PNP.Record285.NumericLink

/-! The remaining hypotheses bind the literal text to the kernel-checked
numeric copies. They are not discharged by a hash or by the generator. -/
namespace Shared.PNP.Record285.NumericEndpoint
open Shared.PNP.Record285.Quotient
open Shared.PNP.Record285.NumericBinding

theorem literal_check (sourceRows targetRows : List RawRow)
    (hsparse : Companion.parse = some sourceRows)
    (hsdata : sourceRows.map companionData = NumericTables.sourceData.toList)
    (htparse : Record285.parse = some targetRows)
    (htdata : targetRows.map markedData = NumericTables.targetData.toList) :
    check (Companion.machine.entering Companion.beepState) Record285.machine
      Companion.quotientMap = true :=
  NumericLink.literal_check_of_parsed sourceRows targetRows hsparse hsdata htparse htdata
    NumericCertificate.numeric_quotient

/-- Assuming the concrete text bindings, every full companion configuration
and event corresponds to a marked-table step, with identity time boundaries. -/
def literal_refinement (sourceRows targetRows : List RawRow)
    (hsparse : Companion.parse = some sourceRows)
    (hsdata : sourceRows.map companionData = NumericTables.sourceData.toList)
    (htparse : Record285.parse = some targetRows)
    (htdata : targetRows.map markedData = NumericTables.targetData.toList) :
    Shared.Beeping.EventRefinement (Companion.machine.entering Companion.beepState).system
      Record285.machine.system :=
  Companion.marked_refinement_of_check (literal_check sourceRows targetRows hsparse hsdata htparse htdata)

theorem literal_silence_iff (sourceRows targetRows : List RawRow)
    (hsparse : Companion.parse = some sourceRows)
    (hsdata : sourceRows.map companionData = NumericTables.sourceData.toList)
    (htparse : Record285.parse = some targetRows)
    (htdata : targetRows.map markedData = NumericTables.targetData.toList) :
    Record285.machine.system.EventuallySilent ↔
      (Companion.machine.exiting Companion.beepState).system.EventuallySilent :=
  Companion.marked_silence_of_check (literal_check sourceRows targetRows hsparse hsdata htparse htdata)

theorem literal_infinite_iff (sourceRows targetRows : List RawRow)
    (hsparse : Companion.parse = some sourceRows)
    (hsdata : sourceRows.map companionData = NumericTables.sourceData.toList)
    (htparse : Record285.parse = some targetRows)
    (htdata : targetRows.map markedData = NumericTables.targetData.toList) :
    Record285.machine.system.InfinitelyManyBeeps ↔
      (Companion.machine.exiting Companion.beepState).system.InfinitelyManyBeeps :=
  Companion.marked_infinite_of_check (literal_check sourceRows targetRows hsparse hsdata htparse htdata)

theorem literal_beep_shift (sourceRows targetRows : List RawRow)
    (hsparse : Companion.parse = some sourceRows)
    (hsdata : sourceRows.map companionData = NumericTables.sourceData.toList)
    (htparse : Record285.parse = some targetRows)
    (htdata : targetRows.map markedData = NumericTables.targetData.toList) (t : Nat) :
    Record285.machine.system.BeepAt t ↔
      (Companion.machine.exiting Companion.beepState).system.BeepAt (t + 1) :=
  Companion.marked_beep_shift_of_check (literal_check sourceRows targetRows hsparse hsdata htparse htdata) t

end Shared.PNP.Record285.NumericEndpoint
