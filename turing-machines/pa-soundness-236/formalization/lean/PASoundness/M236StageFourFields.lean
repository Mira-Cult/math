import PASoundness.M236StageThreeFields

/-! The second coordinate when the scheduled rank is at least two. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def stageRemaining (stage : Nat) : Nat :=
  (Cantor.unpair (Cantor.unpair (Cantor.unpair stage).2).2).2

def stageSecondCoordinate (stage : Nat) : Nat := (Cantor.unpair (stageRemaining stage)).1

def stageFourWord (stage : Nat) : List Bool :=
  stageThreeWord stage ++ PASoundness.UnaryCodec.unary (stageSecondCoordinate stage)

theorem stage_four_word_schedule (stage : Nat) (h : 2 ≤ (Schedule.scheduledAddress stage).rank) :
    stageFourWord stage =
      ((PASoundness.UnaryCodec.unary (Schedule.scheduledAddress stage).rank ++
        PASoundness.UnaryCodec.unary (Schedule.scheduledAddress stage).certificate) ++
          PASoundness.UnaryCodec.unary ((Schedule.scheduledAddress stage).coordinates.headD 0)) ++
            PASoundness.UnaryCodec.unary (((Schedule.scheduledAddress stage).coordinates.drop 1).headD 0) := by
  cases hval : (Cantor.unpair stage).1 with
  | zero => simp [Schedule.scheduledAddress, hval] at h
  | succ n =>
    simp [stageFourWord, stageThreeWord, stageRank, stageSecondCoordinate, stageRemaining,
      Schedule.scheduledAddress, Schedule.decodeCoordinates, hval]

theorem stage_three_exit_registers (base : RegisterMachine.Bank 9) (stage : Nat) (reserve : List Nat)
    (firstPadding padding nextPadding : Nat) :
    (stageThreeExit base stage reserve firstPadding padding nextPadding).registers 3 = (Cantor.unpair stage).1 ∧
    (stageThreeExit base stage reserve firstPadding padding nextPadding).registers 0 = 0 ∧
    (stageThreeExit base stage reserve firstPadding padding nextPadding).registers 6 = 0 ∧
    (stageThreeExit base stage reserve firstPadding padding nextPadding).registers 8 = 0 ∧
    (stageThreeExit base stage reserve firstPadding padding nextPadding).registers 2 = stageRemaining stage := by
  simp [stageThreeExit, thirdFieldExit, cfgFieldTransfer, bankFieldTransfer, bankAS, thirdFieldBank,
    bankAC, bankRest, bankOnlyCount, stageRemaining, stageRankBank, rankBase]

theorem stage_three_exit_to_count_top (base : RegisterMachine.Bank 9) (stage : Nat) (reserve : List Nat)
    (firstPadding padding nextPadding : Nat) :
    stageThreeExit base stage reserve firstPadding padding nextPadding =
      cfgCountTop 79 (stageThreeExit base stage reserve firstPadding padding nextPadding).registers
        (Cantor.unpair stage).1
        ((stageThreeExit base stage reserve firstPadding padding nextPadding).registers 4)
        (stageThreeExit base stage reserve firstPadding padding nextPadding).reserve := by
  have h := cfg_count_top_self 79 (stageThreeExit base stage reserve firstPadding padding nextPadding).registers
    (stageThreeExit base stage reserve firstPadding padding nextPadding).reserve
  rw [(stage_three_exit_registers base stage reserve firstPadding padding nextPadding).1] at h
  exact h.symm

theorem count_top_entry_to_unpair (base : RegisterMachine.Bank 9) (count top : Nat)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) :
    cfgCountTop 84 base count top reserve =
      cfgRAC 84 (bankCountTop base count top) (base 2) 0 0 reserve := by
  unfold cfgCountTop cfgRAC cfgAC
  congr 1
  funext i
  fin_cases i <;> simp [bankCountTop, bankAC, bankRest, ha, hc]

def stageFourthBase (base : RegisterMachine.Bank 9) (stage : Nat) (reserve : List Nat)
    (firstPadding padding nextPadding count : Nat) : RegisterMachine.Bank 9 :=
  let s := stageThreeExit base stage reserve firstPadding padding nextPadding
  bankCountTop s.registers count (s.registers 4)

def stageFourthReserve (base : RegisterMachine.Bank 9) (stage : Nat) (reserve : List Nat)
    (firstPadding padding nextPadding : Nat) : List Nat :=
  (stageThreeExit base stage reserve firstPadding padding nextPadding).reserve ++ [0]

def stageFourExit (base : RegisterMachine.Bank 9) (stage : Nat) (reserve : List Nat)
    (firstPadding padding nextPadding count fourthPadding : Nat) : GraphState :=
  cfgAS 103
    (bankAC (bankRest (stageFourthBase base stage reserve firstPadding padding nextPadding count)
      (Cantor.unpair (stageRemaining stage)).2) (stageSecondCoordinate stage) 0)
    (stageSecondCoordinate stage) 0
    (((stageFourthReserve base stage reserve firstPadding padding nextPadding ++ List.replicate fourthPadding 0) ++
      List.replicate (stageSecondCoordinate stage) 0) ++ List.replicate (stageSecondCoordinate stage) 0)

def stageFourDuration (base : RegisterMachine.Bank 9) (stage firstDuration duration nextDuration fourthDuration : Nat) : Nat :=
  (stageThreeDuration base stage firstDuration duration nextDuration + 2) +
    (fourthDuration + (7*stageSecondCoordinate stage+3))

/-- If the rank is at least two, a clean scheduler entry produces its first
two coordinates in order. The remaining coordinates and value are open. -/
theorem scheduler_first_four_fields (stage count : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = count+1) :
    ∃ firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration fourthPadding,
      stage+1 ≤ firstDuration ∧ (Cantor.unpair stage).2+1 ≤ duration ∧
      (Cantor.unpair (Cantor.unpair stage).2).2+1 ≤ nextDuration ∧
      stageRemaining stage+1 ≤ fourthDuration ∧
      graphSystem.Block (cfg 0 base stage 0 0 reserve)
        (stageFourDuration base stage firstDuration duration nextDuration fourthDuration)
        (stageFourExit base stage reserve firstPadding padding nextPadding count fourthPadding)
        (stageFourWord stage) := by
  obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, hf, hd, hn, block⟩ :=
    scheduler_first_three_fields stage base reserve ha hc hcount
  change graphSystem.Block (cfg 0 base stage 0 0 reserve)
    (stageThreeDuration base stage firstDuration duration nextDuration)
    (stageThreeExit base stage reserve firstPadding padding nextPadding) _ at block
  let s := stageThreeExit base stage reserve firstPadding padding nextPadding
  obtain ⟨_, hs, ha', hc', hr⟩ := stage_three_exit_registers base stage reserve firstPadding padding nextPadding
  change s.registers 0 = 0 at hs
  change s.registers 6 = 0 at ha'
  change s.registers 8 = 0 at hc'
  change s.registers 2 = stageRemaining stage at hr
  rw [stage_three_exit_to_count_top base stage reserve firstPadding padding nextPadding, hpositive] at block
  have hbranch := counter_dispatch_positive 79 counter_dispatch_rows_79 s.registers count (s.registers 4) s.reserve
  have hnext := block.trans graphSystem hbranch
  rw [count_top_entry_to_unpair s.registers count (s.registers 4) (s.reserve ++ [0]) ha' hc', hr] at hnext
  have hscratch : stageFourthBase base stage reserve firstPadding padding nextPadding count 0 = 0 := by
    change bankCountTop s.registers count (s.registers 4) 0 = 0
    simpa [bankCountTop] using hs
  obtain ⟨fourthDuration, fourthPadding, hfourth, hem⟩ :=
    generic_unpair_then_emit (stageRemaining stage) 84 generic_unpair_rows_84 emit_rows_95
      (stageFourthBase base stage reserve firstPadding padding nextPadding count)
      (stageFourthReserve base stage reserve firstPadding padding nextPadding) hscratch
  change graphSystem.Block (cfgRAC 84 (stageFourthBase base stage reserve firstPadding padding nextPadding count)
      (stageRemaining stage) 0 0 (stageFourthReserve base stage reserve firstPadding padding nextPadding))
    (fourthDuration + (7*stageSecondCoordinate stage+3))
    (stageFourExit base stage reserve firstPadding padding nextPadding count fourthPadding) _ at hem
  refine ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding,
    fourthDuration, fourthPadding, hf, hd, hn, hfourth, ?_⟩
  simpa [stageFourDuration, stageFourWord, stageSecondCoordinate, stageFourthBase, stageFourthReserve, s] using
    hnext.trans graphSystem hem

theorem rank_at_least_two_counter (stage : Nat) (h : 2 ≤ (Schedule.scheduledAddress stage).rank) :
    ∃ count, (Cantor.unpair stage).1 = count+1 := by
  cases hval : (Cantor.unpair stage).1 with
  | zero => simp [Schedule.scheduledAddress, hval] at h
  | succ n => exact ⟨n, rfl⟩

/-- The four-field block lifts to the selected literal run at a reached clean
scheduler entry; this does not establish that every entry is reached. -/
theorem selected_scheduler_first_four_fields (i stage count : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = count+1)
    (h : graphSystem.run i = cfg 0 base stage 0 0 reserve) :
    ∃ firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration fourthPadding finish,
      stage+1 ≤ firstDuration ∧ (Cantor.unpair stage).2+1 ≤ duration ∧
      (Cantor.unpair (Cantor.unpair stage).2).2+1 ≤ nextDuration ∧
      stageRemaining stage+1 ≤ fourthDuration ∧ Good finish ∧
      finish.graphState = stageFourExit base stage reserve firstPadding padding nextPadding count fourthPadding ∧
      graphSystem.run (i + stageFourDuration base stage firstDuration duration nextDuration fourthDuration) =
        stageFourExit base stage reserve firstPadding padding nextPadding count fourthPadding ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + stageFourDuration base stage firstDuration duration nextDuration fourthDuration)) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary (i + stageFourDuration base stage firstDuration duration nextDuration fourthDuration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++ stageFourWord stage ∧
      graphRefinement.boundary i <
        graphRefinement.boundary (i + stageFourDuration base stage firstDuration duration nextDuration fourthDuration) := by
  obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    hf, hd, hn, hfourth, block⟩ := scheduler_first_four_fields stage count base reserve ha hc hcount hpositive
  have hr : graphSystem.run (i + stageFourDuration base stage firstDuration duration nextDuration fourthDuration) =
      stageFourExit base stage reserve firstPadding padding nextPadding count fourthPadding := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i + stageFourDuration base stage firstDuration duration nextDuration fourthDuration) =
      graphSystem.prefixWord i ++ stageFourWord stage := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related
    (i + stageFourDuration base stage firstDuration duration nextDuration fourthDuration)
  refine ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    finish, hf, hd, hn, hfourth, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    simp only [stageFourDuration, stageThreeDuration]
    omega

/-- The actual stage-one entry satisfies the rank-two branch and emits its
first two coordinates after the first complete frame. -/
theorem stage_one_first_four_fields_on_selected :
    ∃ i firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration fourthPadding reserve finish,
      Good finish ∧
      graphSystem.run (i + stageFourDuration BlankFirst.zeros 1 firstDuration duration nextDuration fourthDuration) =
        stageFourExit BlankFirst.zeros 1 reserve firstPadding padding nextPadding 0 fourthPadding ∧
      finish.graphState = stageFourExit BlankFirst.zeros 1 reserve firstPadding padding nextPadding 0 fourthPadding ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + stageFourDuration BlankFirst.zeros 1 firstDuration duration nextDuration fourthDuration)) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary (i + stageFourDuration BlankFirst.zeros 1 firstDuration duration nextDuration fourthDuration)) =
        PASoundness.UnaryCodec.encodeFrame ⟨1, 0, [0]⟩ false ++ stageFourWord 1 := by
  obtain ⟨i, _, reserve, _, hstart, _, _, hpstart⟩ := initial_frame_on_selected
  have hpositive : (Cantor.unpair 1).1 = 0+1 := by simp [Cantor.unpair, Cantor.unpairAux]
  obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    finish, _, _, _, _, hg, hs, hr, hconfig, hp, _⟩ :=
      selected_scheduler_first_four_fields i 1 0 BlankFirst.zeros reserve rfl rfl rfl hpositive hstart
  refine ⟨i, firstDuration, firstPadding, duration, padding, nextDuration, nextPadding,
    fourthDuration, fourthPadding, reserve, finish, hg, hr, hs, hconfig, ?_⟩
  simpa [hpstart] using hp

end PASoundness.M236.OccurrenceGraph
