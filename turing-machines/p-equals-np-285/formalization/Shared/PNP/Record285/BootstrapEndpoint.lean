import Shared.PNP.Record285.BootstrapTraceProof

/-! The first blank-start bootstrap, with the full physical tape retained.
The theorem for the literal text exposes its not-yet-proved parsing and row
binding hypotheses. This is only the first phase, not the source refinement. -/
namespace Shared.PNP.Record285.BootstrapEndpoint
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapRows
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.BootstrapTraceProof
open Shared.PNP.Record285.NumericBinding

/-- The generated numeric table leaves the first bootstrap after exactly this
many physical transitions, with this entire tape and no marked events. -/
theorem numeric_bootstrap :
    Rel ⟨exit,(-2 : Int),rep4 1910,true,30⟩
        (NumericTables.target.system.run 2133492) ∧
      ∀ t, t < 2133492 → ¬ NumericTables.target.system.BeepAt t := by
  have h := bootstrap_shape NumericTables.target numeric_rows
  exact silent_physical NumericTables.target (PhysicalNumeric.initial NumericTables.target)
    NumericTables.target.initial (initial_related NumericTables.target rfl)
    2133492 ⟨exit,(-2 : Int),rep4 1910,true,30⟩ h

/-- The corresponding statement for the parsed literal table, conditional on
the two outstanding literal-text binding obligations. -/
theorem literal_bootstrap_of_parsed (parsed : List RawRow)
    (hparse : Record285.parse = some parsed)
    (hdata : parsed.map markedData = NumericTables.targetData.toList) :
    Rel ⟨exit,(-2 : Int),rep4 1910,true,30⟩
        (Record285.machine.system.run 2133492) ∧
      ∀ t, t < 2133492 → ¬ Record285.machine.system.BeepAt t := by
  have h := bootstrap_shape Record285.machine (literal_rows_of_parsed parsed hparse hdata)
  exact silent_physical Record285.machine (PhysicalNumeric.initial Record285.machine)
    Record285.machine.initial (initial_related Record285.machine rfl)
    2133492 ⟨exit,(-2 : Int),rep4 1910,true,30⟩ h

end Shared.PNP.Record285.BootstrapEndpoint
