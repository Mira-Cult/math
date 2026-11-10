import PASoundness.M236StageThreeFields
import PASoundness.M236FinalCleanup
import PASoundness.M236Game

/-! A prepared clean scheduler stage of rank one emits one complete false frame. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

/-- Rank one always uses the selected source's false payoff. -/
theorem selected_rank_one_value (stage : Nat) (h : (Cantor.unpair stage).1 = 0) :
    M236Game.selectedValue (Schedule.scheduledAddress stage) = false := by
  simp [M236Game.selectedValue, Schedule.scheduledAddress, h]

theorem rank_one_word (stage : Nat) (h : (Cantor.unpair stage).1 = 0) :
    stageThreeWord stage ++ [false] =
      PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
        (M236Game.selectedValue (Schedule.scheduledAddress stage)) := by
  simp [stageThreeWord, stageRank, Schedule.scheduledAddress, Schedule.decodeCoordinates,
    M236Game.selectedValue, PASoundness.UnaryCodec.encodeFrame, PASoundness.UnaryCodec.frameFields,
    PASoundness.UnaryCodec.encodeFields, PASoundness.UnaryCodec.unary,
    PASoundness.UnaryCodec.bitNat, h, List.append_assoc]

/-- A prepared clean stage with rank one emits its complete selected-source
frame, then advances to the next completely clean scheduler boundary. -/
theorem scheduler_rank_one_frame (stage : Nat) (reserve : List Nat)
    (h : (Cantor.unpair stage).1 = 0) :
    ∃ duration finalReserve, 0 < duration ∧
      graphSystem.Block (cfg 0 BlankFirst.zeros stage 0 0 reserve) duration
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 finalReserve)
        (PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
          (M236Game.selectedValue (Schedule.scheduledAddress stage))) := by
  have ha : BlankFirst.zeros 6 = 0 := by simp [BlankFirst.zeros]
  have hc : BlankFirst.zeros 8 = 0 := by simp [BlankFirst.zeros]
  have hcount : BlankFirst.zeros 3 = 0 := by simp [BlankFirst.zeros]
  obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding,
    hf, hd, hn, hthree⟩ := scheduler_first_three_fields stage BlankFirst.zeros reserve ha hc hcount
  let exit := stageThreeExit BlankFirst.zeros stage reserve firstPadding padding nextPadding
  change graphSystem.Block (cfg 0 BlankFirst.zeros stage 0 0 reserve)
    (stageThreeDuration BlankFirst.zeros stage firstDuration duration nextDuration) exit
      (stageThreeWord stage) at hthree
  have hexit : exit = cfgCountTop 79 exit.registers 0 (exit.registers 4) exit.reserve := by
    simpa only [exit, stageThreeExit, h] using
      third_exit_to_count_top (stageRankBank BlankFirst.zeros stage) (stageRank stage)
        (stageRankReserve reserve stage firstPadding) padding 0 nextPadding
  rw [hexit] at hthree
  have hdispatch := counter_dispatch_zero (exit.registers 4) 79 counter_dispatch_rows_79 exit.registers exit.reserve
  let bank := bankCountTop exit.registers 0 0
  let r := exit.reserve ++ List.replicate (exit.registers 4) 0
  change graphSystem.Block (cfgCountTop 79 exit.registers 0 (exit.registers 4) exit.reserve)
    (2*(exit.registers 4)+3) (cfgExact 724 bank r) [] at hdispatch
  have hb0 : bank 0 = 0 := by
    simp [bank, bankCountTop, exit, stageThreeExit, thirdFieldExit, cfgFieldTransfer, bankFieldTransfer,
      bankAS, thirdFieldBank, bankAC, bankRest, bankOnlyCount, secondTopState, secondDecodedBank,
      secondFieldBase, bankCountA, stageRankBank, rankBase, bankWith, BlankFirst.zeros]
  have hb3 : bank 3 = 0 := by simp [bank, bankCountTop]
  have hb4 : bank 4 = 0 := by simp [bank, bankCountTop]
  have hb6 : bank 6 = 0 := by simp [bank, bankCountTop, exit, stageThreeExit, thirdFieldExit, cfgFieldTransfer, bankFieldTransfer, bankAS]
  have hb8 : bank 8 = 0 := by
    simp [bank, bankCountTop, exit, stageThreeExit, thirdFieldExit, cfgFieldTransfer, bankFieldTransfer,
      bankAS, thirdFieldBank, bankAC]
  have hb1 : bank 1 = stage := by
    simp [bank, bankCountTop, exit, stageThreeExit, thirdFieldExit, cfgFieldTransfer, bankFieldTransfer,
      bankAS, thirdFieldBank, bankAC, bankRest, bankOnlyCount, secondTopState, secondDecodedBank,
      secondFieldBase, bankCountA, stageRankBank, rankBase, bankWith]
  have hzeroa := WordEventSystem.Block.single graphSystem (cleanup_zero_a bank r hb6)
  have hzerocount := WordEventSystem.Block.single graphSystem (cleanup_zero_count bank r hb3)
  have hfinish := final_cleanup_clean bank r hb0 hb3 hb4 hb6 hb8
  have hblock := (((hthree.trans graphSystem hdispatch).trans graphSystem hzeroa).trans graphSystem hzerocount).trans graphSystem hfinish
  rw [hb1] at hblock
  refine ⟨stageThreeDuration BlankFirst.zeros stage firstDuration duration nextDuration +
    (2*(exit.registers 4)+3) + 1 + 1 + (2*(bank 2+bank 5+bank 7)+6),
    r ++ List.replicate (bank 2+bank 5+bank 7) 0, ?_, ?_⟩
  · dsimp [stageThreeDuration, thirdFieldDuration, secondTopDuration] at *
    omega
  · simpa [rank_one_word stage h] using hblock

/-- The same complete frame appears on the literal selected run if the
prepared rank-one scheduler entry has actually been reached. -/
theorem selected_scheduler_rank_one_frame (i stage : Nat) (reserve : List Nat)
    (hrank : (Cantor.unpair stage).1 = 0)
    (h : graphSystem.run i = cfg 0 BlankFirst.zeros stage 0 0 reserve) :
    ∃ duration finalReserve finish, 0 < duration ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros (stage+1) 0 0 finalReserve ∧
      graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (stage+1) 0 0 finalReserve ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
            (M236Game.selectedValue (Schedule.scheduledAddress stage)) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, finalReserve, ht, block⟩ := scheduler_rank_one_frame stage reserve hrank
  have hrun : graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (stage+1) 0 0 finalReserve := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hword : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i ++
      PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
        (M236Game.selectedValue (Schedule.scheduledAddress stage)) := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hc⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, finalReserve, finish, ht, hg, hs.trans hrun, hrun, hc, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hword]
  · exact graphRefinement.boundary_strict (by omega)

theorem rank_one_stage_two : (Cantor.unpair 2).1 = 0 := by
  simp [Cantor.unpair, Cantor.unpairAux]
theorem scheduled_address_stage_two : Schedule.scheduledAddress 2 = ⟨1, 1, [0]⟩ := by
  simp [Schedule.scheduledAddress, Schedule.decodeCoordinates, Cantor.unpair, Cantor.unpairAux]

/-- Stage two as a prepared graph entry; reachability from blank remains a
separate obligation. -/
theorem prepared_stage_two_frame (reserve : List Nat) :
    ∃ duration finalReserve, 0 < duration ∧
      graphSystem.Block (cfg 0 BlankFirst.zeros 2 0 0 reserve) duration
        (cfg 0 BlankFirst.zeros 3 0 0 finalReserve)
        (PASoundness.UnaryCodec.encodeFrame ⟨1, 1, [0]⟩ false) := by
  simpa [scheduled_address_stage_two, M236Game.selectedValue] using
    scheduler_rank_one_frame 2 reserve rank_one_stage_two

end PASoundness.M236.OccurrenceGraph
