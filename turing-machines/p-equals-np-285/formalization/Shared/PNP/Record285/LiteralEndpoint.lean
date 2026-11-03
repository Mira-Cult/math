import Shared.PNP.Record285.DirectSilentProgress
import Shared.PNP.Record285.ArtifactEndpoint

/-! A single statement binding the literal artifact, designated row, blank
start, perpetual execution and canonical-class endpoint. -/
namespace Shared.PNP.Record285.LiteralEndpoint
open Shared.Beeping

/-- The selected table has the checked rows and event mark, starts on the
wholly blank two-way tape, runs at every finite time, and has the exact
requested canonical P/NP event polarity. -/
theorem selected_literal_endpoint :
    (∀ x, Record285.machine.initial.tape x = false) ∧
    Record285.machine.initial.state.val = 0 ∧ Record285.machine.initial.head = 0 ∧
    (∀ (q : Fin 285) (read : Bool),
      Record285.machine.table.row q read = NumericTables.target.table.row q read) ∧
    (∀ t, Record285.machine.system.BeepAt t ↔
      (Record285.machine.system.run t).state.val = 121 ∧
        (Record285.machine.system.run t).tape (Record285.machine.system.run t).head = true) ∧
    (∀ t, ∃ c, Record285.machine.system.run (t+1) = c) ∧
    (Record285.machine.system.FiniteEventTimes ↔ ComplexityTheory.P = ComplexityTheory.NP) ∧
    (Record285.machine.system.InfinitelyManyBeeps ↔ ComplexityTheory.P ≠ ComplexityTheory.NP) := by
  exact ⟨Record285.blank_start,Record285.start_state,Record285.start_head,
    ArtifactEndpoint.literal_rows,ArtifactEndpoint.literal_beep,Record285.perpetual,
    DirectEndpoint.literal_finiteEvents_iff_P_eq_NP,DirectEndpoint.literal_infinitelyMany_iff_P_ne_NP⟩

end Shared.PNP.Record285.LiteralEndpoint
