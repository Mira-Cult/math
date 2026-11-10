import PASoundness.M236SchedulerRefinement
import PASoundness.M236HistoricalGuard
import PASoundness.M236ObserverFrontDoor

/-! Literal selected M236 and the compact derivation system. These results
stop at compact-system soundness and do not assume a PA translation. -/
namespace PASoundness.M236MachineCompact
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- The literal selected blank-start machine's guarded trace observer accepts
exactly when every compact derivation is sound in the standard coded model. -/
theorem selected_trace_iff_compact_sound :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔ M236Reverse.CompactSound :=
  M236.OccurrenceGraph.scheduler_machine_trace_iff_compact_sound

/-- The separately formalized historical-style first-record observer has the
same exact compact-soundness equivalence. Independent transcription review
against the historical source is a separate question. -/
theorem selected_historical_iff_compact_sound :
    M236HistoricalGuard.HistoricalAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      M236Reverse.CompactSound :=
  M236HistoricalGuard.selected_historicalAccept_iff_traceAccept.trans selected_trace_iff_compact_sound

/-- Explicit observer front door: complete legal records, frame progress,
and a separate winning strategy for every positive-rank game are equivalent
to soundness of the compact derivation system. -/
theorem selected_guards_and_strategies_iff_compact_sound :
    ((Complete (wordDecodedEvents (machineWordSystem M236.machine M236.machineLabels)) ∧
        FrameProgress (machineWordSystem M236.machine M236.machineLabels)) ∧
      ∀ n, 0 < n → ∀ p, ∃ s : Strategy .ex n,
        Winning s (fun xs => Emitted (wordDecodedEvents (machineWordSystem M236.machine M236.machineLabels))
          false ⟨n, p, xs⟩)) ↔ M236Reverse.CompactSound :=
  M236ObserverFrontDoor.selected_trace_iff_complete_and_strategies.symm.trans
    selected_trace_iff_compact_sound

end PASoundness.M236MachineCompact
