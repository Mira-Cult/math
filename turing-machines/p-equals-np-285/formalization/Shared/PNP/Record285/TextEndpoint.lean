import Shared.PNP.Record285.TextCertificate
import Shared.PNP.Record285.BootstrapEndpoint
import Shared.PNP.Record285.Certificate

/-! These interfaces reduce the literal table and first physical bootstrap to
one explicit whole-text equality. No hash or generated output proves that equality. -/
namespace Shared.PNP.Record285.TextEndpoint
open Shared.Beeping.Machines
open Shared.PNP.Record285.TextSegments
open Shared.PNP.Record285.TextCertificate
open Shared.PNP.Record285.NumericBinding
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapRows
open Shared.PNP.Record285.BootstrapSweep

/-- The single remaining literal-to-segments premise. -/
def ArtifactMatches : Prop :=
  Record285.literal = String.ofList (linesChars (header ++ linesFrom0))

/-- Under exact equality with the embedded artifact, all 570 physical rows
agree, including the transition-event bit. -/
theorem literal_rows (h : ArtifactMatches) (q : Fin 285) (read : Bool) :
    Record285.machine.table.row q read = NumericTables.target.table.row q read := by
  obtain ⟨hparse,hdata⟩ := literal_binding h
  exact target_row_of_parsed rowsFrom0 hparse hdata q read

/-- Under the same premise, the sole marked event is the transition from
state 121 reading one. -/
theorem literal_beep (h : ArtifactMatches) (t : Nat) :
    Record285.machine.system.BeepAt t ↔
      (Record285.machine.system.run t).state.val = 121 ∧
        (Record285.machine.system.run t).tape (Record285.machine.system.run t).head = true := by
  obtain ⟨hparse,_⟩ := literal_binding h
  exact Record285.validated_beepAt rowsFrom0 hparse rows_valid t

/-- The same single premise yields the complete-tape first bootstrap result. -/
theorem literal_bootstrap (h : ArtifactMatches) :
    Rel ⟨exit,(-2 : Int),rep4 1910,true,30⟩
        (Record285.machine.system.run 2133492) ∧
      ∀ t, t < 2133492 → ¬ Record285.machine.system.BeepAt t := by
  obtain ⟨hparse,hdata⟩ := literal_binding h
  exact BootstrapEndpoint.literal_bootstrap_of_parsed rowsFrom0 hparse hdata

end Shared.PNP.Record285.TextEndpoint
