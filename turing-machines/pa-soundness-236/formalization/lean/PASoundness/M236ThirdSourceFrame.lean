import PASoundness.M236BoundedTimeout
import PASoundness.M236RankOneFrame

/-! The literal blank-start run through the third complete source frame. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

/-- The actual selected blank-start execution agrees with the repeated-address
source through three complete frames and reaches a clean stage-three graph
boundary. This finite prefix result is not an all-stage source refinement. -/
theorem first_three_source_frames_on_selected :
    ∃ i duration reserve finish, 0 < duration ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros 3 0 0 reserve ∧
      graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros 3 0 0 reserve ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (Source.source M236Game.selectedValue).prefixWord 3 := by
  obtain ⟨i, steps, reserve, _, _, _, _, hrun, _, hprefix⟩ := first_two_source_frames_on_selected
  obtain ⟨duration, finalReserve, finish, ht, hg, hs, hr, hconfig, hword, _⟩ :=
    selected_scheduler_rank_one_frame (i+steps) 2 reserve rank_one_stage_two hrun
  have hsource : (Source.source M236Game.selectedValue).prefixWord 3 =
      (Source.source M236Game.selectedValue).prefixWord 2 ++
        PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress 2)
          (M236Game.selectedValue (Schedule.scheduledAddress 2)) := by
    simp [WordEventSystem.prefix_succ, Source.source]
  refine ⟨i+steps, duration, finalReserve, finish, ht, hg, ?_, ?_, hconfig, ?_⟩
  · simpa using hs
  · simpa using hr
  · rw [hprefix, ← hsource] at hword
    exact hword

end PASoundness.M236.OccurrenceGraph
