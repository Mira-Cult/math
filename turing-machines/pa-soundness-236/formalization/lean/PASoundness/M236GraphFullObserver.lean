import PASoundness.M236GraphOutputRefinement
import PASoundness.M236FrameProgressTransfer
/-! Full guarded-observer equivalence for the retained graph and literal M236. -/
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open PASoundness.Observer PASoundness.UnaryCodec
open Shared.Beeping Shared.Beeping.Machines

theorem graphSystem_physicalBits : graphSystem.PhysicalBits := by
  intro n
  rw [graphSystem_run]
  simp only [graphSystem, selected_graphNext]
  have hp := graph_step_projects _ _ _ _ (segment n).valid
  obtain ⟨edge, op, dest, extra, _, _, hlabel, _, heffect⟩ := hp
  rw [effect_output edge op _ _ _ _ _ hlabel heffect]
  unfold outputForOp
  split_ifs <;> decide

/-- The fixed observer's unfinished-frame guard is preserved in both
directions, even when the ordered output is finite. -/
theorem graph_frameProgress_iff :
    M236Observer.FrameProgress graphSystem ↔
      M236Observer.FrameProgress (machineWordSystem machine machineLabels) :=
  M236Observer.frameProgress_iff_of_sameOutput graphSystem_physicalBits
    (machineWordSystem_physicalBits _ _) graph_sameOutput

/-- Full guarded acceptance of the deterministic retained graph interpreter
is equivalent to acceptance of the literal selected blank-start machine. -/
theorem graph_traceAccept_iff :
    M236Observer.TraceAccept graphSystem ↔
      M236Observer.TraceAccept (machineWordSystem machine machineLabels) :=
  and_congr graph_accept_iff graph_frameProgress_iff
end PASoundness.M236.OccurrenceGraph
