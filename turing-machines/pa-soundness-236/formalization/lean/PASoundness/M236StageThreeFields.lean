import PASoundness.M236SecondStage

/-! The first three scheduled fields at any clean scheduler entry. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def stageRank (stage : Nat) : Nat := (Cantor.unpair stage).1 + 1

def stageRankBank (base : RegisterMachine.Bank 9) (stage : Nat) : RegisterMachine.Bank 9 :=
  rankBase (bankWith base stage stage 0) (Cantor.unpair stage).2 (stageRank stage)

def stageRankReserve (reserve : List Nat) (stage padding : Nat) : List Nat :=
  ((reserve ++ List.replicate stage 0) ++ List.replicate stage 0) ++ List.replicate padding 0

def stageThreeWord (stage : Nat) : List Bool :=
  (PASoundness.UnaryCodec.unary (stageRank stage) ++
    PASoundness.UnaryCodec.unary (Cantor.unpair (Cantor.unpair stage).2).1) ++
      PASoundness.UnaryCodec.unary (Cantor.unpair (Cantor.unpair (Cantor.unpair stage).2).2).1

theorem stage_three_word_schedule (stage : Nat) :
    stageThreeWord stage =
      (PASoundness.UnaryCodec.unary (Schedule.scheduledAddress stage).rank ++
        PASoundness.UnaryCodec.unary (Schedule.scheduledAddress stage).certificate) ++
          PASoundness.UnaryCodec.unary ((Schedule.scheduledAddress stage).coordinates.headD 0) := by
  simp [stageThreeWord, stageRank, Schedule.scheduledAddress, Schedule.decodeCoordinates]

/-- From a clean prepared scheduler entry, the retained graph emits the rank,
certificate, and first coordinate for any stage. It reaches the displayed
entry 79 with exact registers, reserve and finite progress. -/
theorem scheduler_first_three_fields (stage : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0) :
    ∃ firstDuration firstPadding duration padding nextDuration nextPadding,
      stage+1 ≤ firstDuration ∧ (Cantor.unpair stage).2 + 1 ≤ duration ∧
      (Cantor.unpair (Cantor.unpair stage).2).2 + 1 ≤ nextDuration ∧
      graphSystem.Block (cfg 0 base stage 0 0 reserve)
        (((7*stage+2) + firstDuration) +
          thirdFieldDuration (stageRankBank base stage) (stageRank stage) duration nextDuration)
        (thirdFieldExit (stageRankBank base stage) (stageRank stage)
          (stageRankReserve reserve stage firstPadding) padding (Cantor.unpair stage).1 nextPadding)
        (stageThreeWord stage) := by
  have hcopy : graphSystem.Block (cfg 0 base stage 0 0 reserve) (7*stage+2)
      (cfg 7 base stage stage 0 ((reserve ++ List.replicate stage 0) ++ List.replicate stage 0)) [] := by
    simpa only [Nat.zero_add] using copy_stage stage base 0 reserve
  rw [copy_exit_to_unpair base stage _ ha hc] at hcopy
  obtain ⟨firstDuration, firstPadding, hfirst, hscan⟩ :=
    unpair_to_rank_entry stage (bankWith base stage stage 0)
      ((reserve ++ List.replicate stage 0) ++ List.replicate stage 0)
  rw [rank_entry_convert (bankWith base stage stage 0) (Cantor.unpair stage).2
    ((Cantor.unpair stage).1+1) _ (by simp [bankWith])] at hscan
  change graphSystem.Block (cfgRAC 7 (bankWith base stage stage 0) stage 0 0 _)
    firstDuration (cfgAS 19 (stageRankBank base stage) (stageRank stage) 0
      (stageRankReserve reserve stage firstPadding)) [] at hscan
  have hc' : stageRankBank base stage 8 = 0 := by simp [stageRankBank, rankBase, bankAC]
  have hcount' : stageRankBank base stage 3 + stageRank stage = (Cantor.unpair stage).1 + 1 := by
    simp [stageRankBank, rankBase, bankAC, bankRest, bankWith, stageRank, hcount]
  have hrest : stageRankBank base stage 2 = (Cantor.unpair stage).2 := by
    simp [stageRankBank, rankBase, bankAC, bankRest]
  obtain ⟨duration, padding, nextDuration, nextPadding, hd, hn, hfields⟩ :=
    rank_through_third_field (stageRank stage) (Cantor.unpair stage).1
      (stageRankBank base stage) (stageRankReserve reserve stage firstPadding) hc' hcount'
  change graphSystem.Block (cfgAS 19 (stageRankBank base stage) (stageRank stage) 0
      (stageRankReserve reserve stage firstPadding))
    (thirdFieldDuration (stageRankBank base stage) (stageRank stage) duration nextDuration)
    (thirdFieldExit (stageRankBank base stage) (stageRank stage)
      (stageRankReserve reserve stage firstPadding) padding (Cantor.unpair stage).1 nextPadding) _ at hfields
  have hword : (PASoundness.UnaryCodec.unary (stageRank stage) ++
      PASoundness.UnaryCodec.unary (Cantor.unpair (stageRankBank base stage 2)).1) ++
      PASoundness.UnaryCodec.unary (thirdFieldValue (stageRankBank base stage)) = stageThreeWord stage := by
    simp [stageThreeWord, thirdFieldValue, hrest]
  rw [hword] at hfields
  refine ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding,
    hfirst, ?_, ?_, ?_⟩
  · simpa only [hrest] using hd
  · simpa only [hrest] using hn
  · simpa only [List.nil_append, Nat.add_assoc] using (hcopy.trans graphSystem hscan).trans graphSystem hfields

def stageThreeDuration (base : RegisterMachine.Bank 9) (stage firstDuration duration nextDuration : Nat) : Nat :=
  ((7*stage+2) + firstDuration) +
    thirdFieldDuration (stageRankBank base stage) (stageRank stage) duration nextDuration

def stageThreeExit (base : RegisterMachine.Bank 9) (stage : Nat) (reserve : List Nat)
    (firstPadding padding nextPadding : Nat) : GraphState :=
  thirdFieldExit (stageRankBank base stage) (stageRank stage)
    (stageRankReserve reserve stage firstPadding) padding (Cantor.unpair stage).1 nextPadding

/-- On any reached clean scheduler boundary, the literal selected execution
produces the same three fields in order and reaches the displayed graph state. -/
theorem selected_scheduler_first_three_fields (i stage : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (h : graphSystem.run i = cfg 0 base stage 0 0 reserve) :
    ∃ firstDuration firstPadding duration padding nextDuration nextPadding finish,
      stage+1 ≤ firstDuration ∧ (Cantor.unpair stage).2+1 ≤ duration ∧
      (Cantor.unpair (Cantor.unpair stage).2).2+1 ≤ nextDuration ∧ Good finish ∧
      finish.graphState = stageThreeExit base stage reserve firstPadding padding nextPadding ∧
      graphSystem.run (i + stageThreeDuration base stage firstDuration duration nextDuration) =
        stageThreeExit base stage reserve firstPadding padding nextPadding ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + stageThreeDuration base stage firstDuration duration nextDuration)) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary (i + stageThreeDuration base stage firstDuration duration nextDuration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++ stageThreeWord stage ∧
      graphRefinement.boundary i <
        graphRefinement.boundary (i + stageThreeDuration base stage firstDuration duration nextDuration) := by
  obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, hf, hd, hn, block⟩ :=
    scheduler_first_three_fields stage base reserve ha hc hcount
  change graphSystem.Block (cfg 0 base stage 0 0 reserve)
    (stageThreeDuration base stage firstDuration duration nextDuration)
    (stageThreeExit base stage reserve firstPadding padding nextPadding) _ at block
  have hr : graphSystem.run (i + stageThreeDuration base stage firstDuration duration nextDuration) =
      stageThreeExit base stage reserve firstPadding padding nextPadding := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i + stageThreeDuration base stage firstDuration duration nextDuration) =
      graphSystem.prefixWord i ++ stageThreeWord stage := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related
    (i + stageThreeDuration base stage firstDuration duration nextDuration)
  refine ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, finish,
    hf, hd, hn, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    simp only [stageThreeDuration]
    omega

end PASoundness.M236.OccurrenceGraph
