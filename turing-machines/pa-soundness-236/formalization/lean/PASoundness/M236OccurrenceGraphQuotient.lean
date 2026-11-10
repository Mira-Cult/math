import PASoundness.M236OccurrenceGraphWalk
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236
open Shared.Beeping Shared.Beeping.Machines

/-- Each graph step preserves the exact event word on the selected quotient. -/
theorem graph_step_selected_block (a b : Snapshot) (duration : Nat) (events : List Bool)
    (h : GraphStep a b duration events) :
    (machineWordSystem machine machineLabels).Block (mapConfig a.config) duration (mapConfig b.config) events := by
  obtain ⟨ha, hb, edge, op, dest, extra, hpath, heffect, hsuccessor, hi, hrow, hlabel, hbranch, ht, hblock⟩ := h
  exact BootstrapScan.mapped_block hblock
end PASoundness.M236.OccurrenceGraph
