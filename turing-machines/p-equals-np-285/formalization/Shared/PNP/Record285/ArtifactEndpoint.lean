import Shared.PNP.Record285.ArtifactCertificate

/-! Unconditional physical statements for the embedded 285-state artifact.
This does not establish the full physical-to-source refinement or P = NP. -/
namespace Shared.PNP.Record285.ArtifactEndpoint
open Shared.Beeping.Machines
open Shared.PNP.Record285.TextCertificate
open Shared.PNP.Record285.ArtifactCertificate
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapRows
open Shared.PNP.Record285.BootstrapSweep

/-- Parsing of the actual embedded file succeeds with the checked 570 rows. -/
theorem literal_parse : Record285.parse = some rowsFrom0 :=
  (TextCertificate.literal_binding artifactMatches).1

/-- The actual embedded file satisfies all ordering, bounds and event checks. -/
theorem literal_valid : Record285.wellFormed rowsFrom0 = true := rows_valid

/-- Every physical row, including its mark, is the selected numeric row. -/
theorem literal_rows (q : Fin 285) (read : Bool) :
    Record285.machine.table.row q read = NumericTables.target.table.row q read :=
  TextEndpoint.literal_rows artifactMatches q read

/-- The only marked event is taking the row for state 121 and symbol 1. -/
theorem literal_beep (t : Nat) :
    Record285.machine.system.BeepAt t ↔
      (Record285.machine.system.run t).state.val = 121 ∧
        (Record285.machine.system.run t).tape (Record285.machine.system.run t).head = true :=
  TextEndpoint.literal_beep artifactMatches t

/-- Exact first-phase blank-start physical run, including every tape cell and
absolute head position, with no events in its 2,133,492 transitions. -/
theorem literal_bootstrap :
    Rel ⟨exit,(-2 : Int),rep4 1910,true,30⟩
        (Record285.machine.system.run 2133492) ∧
      ∀ t, t < 2133492 → ¬ Record285.machine.system.BeepAt t :=
  TextEndpoint.literal_bootstrap artifactMatches

end Shared.PNP.Record285.ArtifactEndpoint
