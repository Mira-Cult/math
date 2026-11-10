import PASoundness.M236FirstFrame

/-! Continue the actual blank-start execution from the first clean stage entry. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def stageOneRankBank : RegisterMachine.Bank 9 :=
  rankBase (bankWith BlankFirst.zeros 1 1 0) 0 2

def stageOneRankReserve (reserve : List Nat) (padding : Nat) : List Nat :=
  ((((reserve ++ List.replicate 1 0) ++ List.replicate 1 0) ++ List.replicate padding 0) ++
    List.replicate 2 0) ++ List.replicate 2 0

/-- After its first complete frame, the selected blank-start run emits the
rank-two unary header of stage 1. The remaining fields and value are open. -/
theorem second_stage_rank_on_selected :
    ∃ i duration padding reserve finish,
      2 ≤ duration ∧ Good finish ∧
      graphSystem.run (i + (9 + (duration + 17))) =
        cfgAS 27 stageOneRankBank 2 0 (stageOneRankReserve reserve padding) ∧
      finish.graphState = cfgAS 27 stageOneRankBank 2 0 (stageOneRankReserve reserve padding) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + (9 + (duration + 17)))) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary (i + (9 + (duration + 17)))) =
        PASoundness.UnaryCodec.encodeFrame ⟨1, 0, [0]⟩ false ++ PASoundness.UnaryCodec.unary 2 ∧
      graphRefinement.boundary i < graphRefinement.boundary (i + (9 + (duration + 17))) := by
  obtain ⟨i, _, reserve, _, hstart, _, _, hpstart⟩ := initial_frame_on_selected
  have hpgraph : graphSystem.prefixWord i = PASoundness.UnaryCodec.encodeFrame ⟨1, 0, [0]⟩ false := by
    simpa only [graphRefinement.prefix_eq] using hpstart
  obtain ⟨duration, padding, hd, block⟩ := scheduler_rank_field 1 BlankFirst.zeros reserve rfl rfl
  have block' : graphSystem.Block (cfg 0 BlankFirst.zeros 1 0 0 reserve) (9 + (duration + 17))
      (cfgAS 27 stageOneRankBank 2 0 (stageOneRankReserve reserve padding))
      (PASoundness.UnaryCodec.unary 2) := by
    simpa [stageOneRankBank, stageOneRankReserve, Cantor.unpair, Cantor.unpairAux] using block
  have hr : graphSystem.run (i + (9 + (duration + 17))) =
      cfgAS 27 stageOneRankBank 2 0 (stageOneRankReserve reserve padding) := by
    rw [WordEventSystem.run_add, hstart, block'.endpoint]
  have hp : graphSystem.prefixWord (i + (9 + (duration + 17))) =
      PASoundness.UnaryCodec.encodeFrame ⟨1, 0, [0]⟩ false ++ PASoundness.UnaryCodec.unary 2 := by
    rw [WordEventSystem.prefix_add, hstart, block'.output, hpgraph]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i + (9 + (duration + 17)))
  refine ⟨i, duration, padding, reserve, finish, by omega, hg, hr, hs.trans hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
