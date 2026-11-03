import Shared.PNP.Record285.CompanionArtifactCertificate
import Shared.PNP.Record285.ArtifactEndpoint
import Shared.PNP.Record285.NumericEndpoint

/-! Unconditional event-preserving quotient between the two frozen literal
artifacts. This is not the missing refinement from either machine to the source. -/
namespace Shared.PNP.Record285.LiteralQuotient
open Shared.PNP.Record285.Quotient
open Shared.PNP.Record285.NumericBinding

theorem companion_parse : Companion.parse = some CompanionTextCertificate.rowsFrom0 :=
  (CompanionTextCertificate.literal_binding CompanionArtifactCertificate.artifactMatches).1

theorem companion_data : CompanionTextCertificate.rowsFrom0.map companionData =
    NumericTables.sourceData.toList := CompanionTextCertificate.numeric_data

theorem marked_parse : Record285.parse = some TextCertificate.rowsFrom0 :=
  ArtifactEndpoint.literal_parse

theorem marked_data : TextCertificate.rowsFrom0.map markedData =
    NumericTables.targetData.toList := TextCertificate.numeric_data

/-- Every 286-state row passes the event-coloured quotient checker against the
literal marked table, including both raw preimages of merged state 1. -/
theorem check : Quotient.check (Companion.machine.entering Companion.beepState)
    Record285.machine Companion.quotientMap = true :=
  NumericEndpoint.literal_check CompanionTextCertificate.rowsFrom0 TextCertificate.rowsFrom0
    companion_parse companion_data marked_parse marked_data

/-- Step-for-step full-tape refinement, with identical event boundaries. -/
def refinement :
    Shared.Beeping.EventRefinement (Companion.machine.entering Companion.beepState).system
      Record285.machine.system := Companion.marked_refinement_of_check check

/-- Each marked event is exactly one transition before the companion B-exit. -/
theorem beep_shift (t : Nat) :
    Record285.machine.system.BeepAt t ↔
      (Companion.machine.exiting Companion.beepState).system.BeepAt (t+1) :=
  Companion.marked_beep_shift_of_check check t

theorem silence_iff :
    Record285.machine.system.EventuallySilent ↔
      (Companion.machine.exiting Companion.beepState).system.EventuallySilent :=
  Companion.marked_silence_of_check check

theorem infinite_iff :
    Record285.machine.system.InfinitelyManyBeeps ↔
      (Companion.machine.exiting Companion.beepState).system.InfinitelyManyBeeps :=
  Companion.marked_infinite_of_check check

end Shared.PNP.Record285.LiteralQuotient
