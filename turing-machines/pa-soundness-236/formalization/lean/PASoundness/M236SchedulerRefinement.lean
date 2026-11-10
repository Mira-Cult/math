import PASoundness.M236SchedulerAtom
import PASoundness.M236CoveredRefinement
import PASoundness.M236SourceGraphBridge

/-! Exhaustive clean scheduler frames, their coherent source refinement, and
exact transfer to the existing selected-machine observer. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open PASoundness.Observer PASoundness.UnaryCodec
open Shared.Beeping Shared.Beeping.Machines

/-- Rank one, successful-budget, and overflow cases cover every scheduler
stage and every finite reserve. The old narrow `CoveredStage` predicate is
not used. -/
theorem scheduler_all_frame_blocks : StageFrameBlocks := by
  intro stage reserve
  by_cases hz : (Cantor.unpair stage).1 = 0
  · exact scheduler_rank_one_frame stage reserve hz
  · let count := (Cantor.unpair stage).1 - 1
    have hpositive : (Cantor.unpair stage).1 = count+1 := by dsimp [count]; omega
    by_cases hbudget : stageSecondCoordinate stage ≤ count
    · exact scheduler_bounded_frame stage count reserve hpositive hbudget
    · have hoverflow : stageSecondCoordinate stage = count + (stageSecondCoordinate stage-count-1) + 1 := by omega
      exact scheduler_overflow_frame stage count (stageSecondCoordinate stage-count-1)
        BlankFirst.zeros reserve rfl rfl rfl hpositive hoverflow

/-- Coherent source-to-graph refinement of the actual clean graph start. -/
noncomputable def sourceGraphRefinement :
    WordRefinement (Source.source M236Game.selectedValue) graphSystem :=
  schedulerGraphRefinement scheduler_all_frame_blocks

/-- The same source refines the literal selected machine's full ordered wire. -/
noncomputable def sourceMachineRefinement :
    WordRefinement (Source.source M236Game.selectedValue)
      (machineWordSystem machine machineLabels) :=
  schedulerMachineRefinement scheduler_all_frame_blocks

theorem source_graph_sameOutput : SameOutput (Source.source M236Game.selectedValue) graphSystem :=
  sourceGraphRefinement.sameOutput

theorem source_machine_sameOutput :
    SameOutput (Source.source M236Game.selectedValue) (machineWordSystem machine machineLabels) :=
  sourceMachineRefinement.sameOutput

/-- The graph satisfies the unfinished-frame progress guard independently of
whether its observer accepts. -/
theorem scheduler_graph_frame_progress : M236Observer.FrameProgress graphSystem :=
  M236SourceGraphBridge.graph_frame_progress_of_refinement M236Game.selectedValue sourceGraphRefinement

theorem scheduler_machine_frame_progress :
    M236Observer.FrameProgress (machineWordSystem machine machineLabels) :=
  graph_frameProgress_forward scheduler_graph_frame_progress

theorem scheduler_graph_trace_iff_source :
    M236Observer.TraceAccept graphSystem ↔
      M236Observer.TraceAccept (Source.source M236Game.selectedValue) :=
  M236SourceGraphBridge.graph_trace_iff_source M236Game.selectedValue sourceGraphRefinement

theorem scheduler_machine_trace_iff_source :
    M236Observer.TraceAccept (machineWordSystem machine machineLabels) ↔
      M236Observer.TraceAccept (Source.source M236Game.selectedValue) :=
  graph_traceAccept_iff.symm.trans scheduler_graph_trace_iff_source

theorem scheduler_graph_trace_iff_compact_sound :
    M236Observer.TraceAccept graphSystem ↔ M236Reverse.CompactSound :=
  scheduler_graph_trace_iff_source.trans M236Reverse.source_accept_iff_compact_sound

/-- This is compact-calculus soundness, not yet a claim about a PA proof
translation or another definition of omega acceptance. -/
theorem scheduler_machine_trace_iff_compact_sound :
    M236Observer.TraceAccept (machineWordSystem machine machineLabels) ↔ M236Reverse.CompactSound :=
  M236SourceGraphBridge.physical_iff_compact_sound_of_source_refinement sourceGraphRefinement

end PASoundness.M236.OccurrenceGraph
