import PASoundness.M236BoundedInitialization
import PASoundness.M236FinalCleanup
import PASoundness.M236OverflowFrame

/-! Count-zero exits after the bounded initial-bit selection. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def timeoutBank (base : RegisterMachine.Bank 9) (b top : Nat) : RegisterMachine.Bank 9 :=
  fun i => if i = 7 then b else if i = 4 then top else base i

def cfgTimeout (i : Nat) (base : RegisterMachine.Bank 9) (b top : Nat) (reserve : List Nat) : GraphState :=
  ⟨i, timeoutBank base b top, reserve⟩

theorem timeout_rows_163 : CounterDispatchRows 163 := by constructor <;> decide
theorem timeout_rows_369 : CounterDispatchRows 369 := by constructor <;> decide
theorem timeout_row161 : sourceRows[161]? = some ("3.k.b.decnz", 162, some 163) := by decide
theorem timeout_row162 : sourceRows[162]? = some ("jump", 366, none) := by decide
theorem timeout_row366 : sourceRows[366]? = some ("3.k.top.decnz", 367, some 369) := by decide
theorem timeout_row367 : sourceRows[367]? = some ("3.k.b.inc", 368, none) := by decide
theorem timeout_row368 : sourceRows[368]? = some ("jump", 366, none) := by decide

theorem timeout_bit_zero (base : RegisterMachine.Bank 9) (top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgTimeout 161 base 0 top reserve) = (cfgTimeout 163 base 0 top reserve, []) := by
  simp [graphSystem, graphNext, cfgTimeout, timeout_row161, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, timeoutBank, RegisterMachine.execute]

theorem timeout_bit_one (base : RegisterMachine.Bank 9) (top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgTimeout 161 base 1 top reserve) = (cfgTimeout 162 base 0 top (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgTimeout, timeout_row161, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, timeoutBank, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [timeoutBank, RegisterMachine.write])

theorem timeout_jump162 (base : RegisterMachine.Bank 9) (b top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgTimeout 162 base b top reserve) = (cfgTimeout 366 base b top reserve, []) := by
  simp [graphSystem, graphNext, cfgTimeout, timeout_row162, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem timeout_dec_top (base : RegisterMachine.Bank 9) (b top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgTimeout 366 base b (top+1) reserve) =
      (cfgTimeout 367 base b top (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgTimeout, timeout_row366, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, timeoutBank, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [timeoutBank, RegisterMachine.write])

theorem timeout_zero_top (base : RegisterMachine.Bank 9) (b : Nat) (reserve : List Nat) :
    graphSystem.step (cfgTimeout 366 base b 0 reserve) = (cfgTimeout 369 base b 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgTimeout, timeout_row366, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, timeoutBank, RegisterMachine.execute]

theorem timeout_inc_b (base : RegisterMachine.Bank 9) (b top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgTimeout 367 base b top reserve) = (cfgTimeout 368 base (b+1) top reserve, []) := by
  simp [graphSystem, graphNext, cfgTimeout, timeout_row367, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, timeoutBank, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [timeoutBank, RegisterMachine.write])

theorem timeout_jump368 (base : RegisterMachine.Bank 9) (b top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgTimeout 368 base b top reserve) = (cfgTimeout 366 base b top reserve, []) := by
  simp [graphSystem, graphNext, cfgTimeout, timeout_row368, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem timeout_move_top (n : Nat) (base : RegisterMachine.Bank 9) (b : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgTimeout 366 base b n reserve) (3*n+1)
      (cfgTimeout 369 base (b+n) 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing b reserve with
  | zero => simpa using WordEventSystem.Block.single graphSystem (timeout_zero_top base b reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (timeout_dec_top base b n reserve)
    have h2 := WordEventSystem.Block.single graphSystem (timeout_inc_b base b n (reserve ++ [0]))
    have h3 := WordEventSystem.Block.single graphSystem (timeout_jump368 base (b+1) n (reserve ++ [0]))
    have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem (ih (b+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem timeout_count_view (i : Nat) (base : RegisterMachine.Bank 9) (b top : Nat) (reserve : List Nat) :
    cfgTimeout i base b top reserve = cfgCountTop i (timeoutBank base b top) (base 3) top reserve := by
  unfold cfgTimeout cfgCountTop
  congr 1
  funext i
  fin_cases i <;> simp [timeoutBank, bankCountTop]

theorem timeout_count_zero_exit (i : Nat) (base : RegisterMachine.Bank 9) (b top : Nat)
    (reserve : List Nat) (hc : base 3 = 0) :
    cfgTimeout i base b top reserve = cfgCountTop i (timeoutBank base b top) 0 top reserve := by
  simpa [hc] using timeout_count_view i base b top reserve

theorem timeout_zero_to_cleanup (top : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 3 = 0) :
    graphSystem.Block (cfgTimeout 161 base 0 top reserve) (2*top+4)
      (cfgTimeout 724 base 0 0 (reserve ++ List.replicate top 0)) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (timeout_bit_zero base top reserve)
  rw [timeout_count_zero_exit 163 base 0 top reserve hc] at h1
  have h2 := counter_dispatch_zero top 163 timeout_rows_163 (timeoutBank base 0 top) reserve
  have h := h1.trans graphSystem h2
  have hout : cfgCountTop 724 (timeoutBank base 0 top) 0 0 (reserve ++ List.replicate top 0) =
      cfgTimeout 724 base 0 0 (reserve ++ List.replicate top 0) := by
    unfold cfgCountTop cfgTimeout
    congr 1
    funext i
    fin_cases i <;> simp [bankCountTop, timeoutBank, hc]
  rw [hout] at h
  have ht : 1+(2*top+3) = 2*top+4 := by omega
  simpa [ht] using h

theorem timeout_one_to_cleanup (top : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 3 = 0) :
    graphSystem.Block (cfgTimeout 161 base 1 top reserve) (3*top+6)
      (cfgTimeout 724 base top 0 (reserve ++ List.replicate (top+1) 0)) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (timeout_bit_one base top reserve)
  have h2 := WordEventSystem.Block.single graphSystem (timeout_jump162 base 0 top (reserve ++ [0]))
  have h3 := timeout_move_top top base 0 (reserve ++ [0])
  simp only [Nat.zero_add] at h3
  rw [timeout_count_zero_exit 369 base top 0 _ hc] at h3
  have h4 := counter_dispatch_zero 0 369 timeout_rows_369 (timeoutBank base top 0)
    ((reserve ++ [0]) ++ List.replicate top 0)
  have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4
  have hout : cfgCountTop 724 (timeoutBank base top 0) 0 0
      (((reserve ++ [0]) ++ List.replicate top 0) ++ List.replicate 0 0) =
      cfgTimeout 724 base top 0 (reserve ++ List.replicate (top+1) 0) := by
    have hr : ((reserve ++ [0]) ++ List.replicate top 0) ++ List.replicate 0 0 =
        reserve ++ List.replicate (top+1) 0 := by
      simp [List.replicate_succ, List.append_assoc]
    rw [hr]
    unfold cfgCountTop cfgTimeout
    congr 1
    funext i
    fin_cases i <;> simp [bankCountTop, timeoutBank, hc]
  rw [hout] at h
  have ht : 1+1+(3*top+1)+(2*0+3) = 3*top+6 := by omega
  simpa [ht] using h

/-- From row 724 with exhausted count and clean work registers, the general
final cleanup handles arbitrary rest/env/b and emits a single false bit. -/
theorem timeout_final_cleanup (base : RegisterMachine.Bank 9) (b : Nat) (reserve : List Nat)
    (h0 : base 0 = 0) (h3 : base 3 = 0) (h6 : base 6 = 0) (h8 : base 8 = 0) :
    graphSystem.Block (cfgTimeout 724 base b 0 reserve) (2*(base 2+base 5+b)+8)
      (cfg 0 BlankFirst.zeros (base 1+1) 0 0
        (reserve ++ List.replicate (base 2+base 5+b) 0)) [false] := by
  let bank := timeoutBank base b 0
  have hb0 : bank 0 = 0 := by simp [bank, timeoutBank, h0]
  have hb3 : bank 3 = 0 := by simp [bank, timeoutBank, h3]
  have hb4 : bank 4 = 0 := by simp [bank, timeoutBank]
  have hb6 : bank 6 = 0 := by simp [bank, timeoutBank, h6]
  have hb8 : bank 8 = 0 := by simp [bank, timeoutBank, h8]
  have h1 := WordEventSystem.Block.single graphSystem (cleanup_zero_a bank reserve hb6)
  have h2 := WordEventSystem.Block.single graphSystem (cleanup_zero_count bank reserve hb3)
  have h3' := final_cleanup_clean bank reserve hb0 hb3 hb4 hb6 hb8
  have h := (h1.trans graphSystem h2).trans graphSystem h3'
  have ht : 1+1+(2*(bank 2+bank 5+bank 7)+6) = 2*(bank 2+bank 5+bank 7)+8 := by omega
  rw [ht] at h
  simpa [cfgTimeout, cfgExact, bank, timeoutBank] using h

/-- At row 161 with a zero count, both possible selected bits take a finite
silent timeout path; they then emit false and return to a clean next stage. -/
theorem timeout_false_frame (bit : Bool) (base : RegisterMachine.Bank 9) (top : Nat)
    (reserve : List Nat) (h0 : base 0 = 0) (h3 : base 3 = 0)
    (h6 : base 6 = 0) (h8 : base 8 = 0) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgTimeout 161 base (if bit then 1 else 0) top reserve) duration
        (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0)) [false] := by
  cases bit with
  | false =>
    have h1 := timeout_zero_to_cleanup top base reserve h3
    have h2 := timeout_final_cleanup base 0 (reserve ++ List.replicate top 0) h0 h3 h6 h8
    have h := h1.trans graphSystem h2
    refine ⟨(2*top+4)+(2*(base 2+base 5+0)+8), top+(base 2+base 5+0), by omega, ?_⟩
    have hr : (reserve ++ List.replicate top 0) ++ List.replicate (base 2+base 5+0) 0 =
        reserve ++ List.replicate (top+(base 2+base 5+0)) 0 := by
      simp only [List.append_assoc, ← List.replicate_add]
    rw [hr] at h
    simpa using h
  | true =>
    have h1 := timeout_one_to_cleanup top base reserve h3
    have h2 := timeout_final_cleanup base top (reserve ++ List.replicate (top+1) 0) h0 h3 h6 h8
    have h := h1.trans graphSystem h2
    refine ⟨(3*top+6)+(2*(base 2+base 5+top)+8), (top+1)+(base 2+base 5+top), by omega, ?_⟩
    have hr : (reserve ++ List.replicate (top+1) 0) ++ List.replicate (base 2+base 5+top) 0 =
        reserve ++ List.replicate ((top+1)+(base 2+base 5+top)) 0 := by
      simp only [List.append_assoc, ← List.replicate_add]
    rw [hr] at h
    simpa using h

/-- Physical lift for either selected bit, conditional on reaching the
prepared count-zero graph state. -/
theorem selected_timeout_false_frame (i : Nat) (bit : Bool) (base : RegisterMachine.Bank 9)
    (top : Nat) (reserve : List Nat) (h0 : base 0 = 0) (h3 : base 3 = 0)
    (h6 : base 6 = 0) (h8 : base 8 = 0)
    (h : graphSystem.run i = cfgTimeout 161 base (if bit then 1 else 0) top reserve) :
    ∃ duration padding finish, 0 < duration ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++ [false] ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := timeout_false_frame bit base top reserve h0 h3 h6 h8
  have hr : graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i ++ [false] := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hstate, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hstate.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

/-- If the prepared budget exit has exhausted its counter, bit extraction,
environment initialization, both timeout branches and final cleanup compose to
one false-bit frame suffix and a clean next-stage entry. -/
theorem budget_exit_count_zero_frame (n env : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hs : base 0 = 0) :
    ∃ duration padding, n+2 ≤ duration ∧
      graphSystem.Block (cfgBudget 119 base 0 env n 0 reserve) duration
        (cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0)) [false] := by
  obtain ⟨d1, p1, hd1, h1⟩ := budget_exit_then_initialize n 0 env base reserve hs
  let E := budgetExitBitBank base 0 env n
  let bank := bankBudget E 0 (Cantor.pair env 0) 0 0
  let bit := (base 7).testBit n
  have hview : cfgBudget 161 E 0 (Cantor.pair env 0) 0 0 (reserve ++ List.replicate p1 0) =
      cfgTimeout 161 bank (if bit then 1 else 0) (base 4) (reserve ++ List.replicate p1 0) := by
    unfold cfgBudget cfgTimeout
    congr 1
    funext i
    fin_cases i <;> simp [bank, E, bit, budgetExitBitBank, bankBudget, bankHalf, timeoutBank]
  rw [hview] at h1
  have h0 : bank 0 = 0 := by simp [bank, E, budgetExitBitBank, bankBudget, bankHalf]
  have h3 : bank 3 = 0 := by simp [bank, bankBudget]
  have h6 : bank 6 = 0 := by simp [bank, bankBudget]
  have h8 : bank 8 = 0 := by simp [bank, bankBudget]
  have hstage : bank 1 = base 1 := by simp [bank, E, budgetExitBitBank, bankBudget, bankHalf]
  obtain ⟨d2, p2, hd2, h2⟩ := timeout_false_frame bit bank (base 4)
    (reserve ++ List.replicate p1 0) h0 h3 h6 h8
  have h := h1.trans graphSystem h2
  rw [hstage] at h
  refine ⟨d1+d2, p1+p2, by omega, ?_⟩
  have hr : (reserve ++ List.replicate p1 0) ++ List.replicate p2 0 =
      reserve ++ List.replicate (p1+p2) 0 := by
    simp only [List.append_assoc, ← List.replicate_add]
  rw [hr] at h
  simpa using h

/-- Physical lift of the prepared count-zero budget exit. -/
theorem selected_budget_exit_count_zero_frame (i n env : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hs : base 0 = 0)
    (h : graphSystem.run i = cfgBudget 119 base 0 env n 0 reserve) :
    ∃ duration padding finish, n+2 ≤ duration ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++ [false] ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := budget_exit_count_zero_frame n env base reserve hs
  have hr : graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (base 1+1) 0 0 (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i ++ [false] := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hstate, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hstate.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

/-- Rank-two records have no remaining game moves and therefore have false
selected value. This is an abstract source fact, independent of graph runs. -/
theorem rank_two_selected_value_false (stage : Nat) (hpositive : (Cantor.unpair stage).1 = 1) :
    M236Game.selectedValue (Schedule.scheduledAddress stage) = false := by
  simp [M236Game.selectedValue, Schedule.scheduledAddress, Schedule.decodeCoordinates,
    hpositive, M236Game.aligned, M236Game.path]

/-- A rank-two clean scheduler entry whose second coordinate is within its
zero remaining budget emits exactly its selected source frame and returns to
a clean next-stage entry. -/
theorem scheduler_rank_two_bounded_frame (stage : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = 1)
    (hbudget : stageSecondCoordinate stage = 0) :
    ∃ steps nextReserve, 0 < steps ∧
      graphSystem.Block (cfg 0 base stage 0 0 reserve) steps
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve)
        (PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
          (M236Game.selectedValue (Schedule.scheduledAddress stage))) := by
  have hpos : (Cantor.unpair stage).1 = 0+1 := by simpa using hpositive
  obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    hf, hd, hn, hfourth, hfour⟩ :=
    scheduler_first_four_fields stage 0 base reserve ha hc hcount hpos
  let b := stageFourBudgetBank base stage reserve firstPadding padding nextPadding 0
  let r := stageFourBudgetReserve base stage reserve firstPadding padding nextPadding fourthPadding
  change graphSystem.Block (cfg 0 base stage 0 0 reserve) _
    (cfgAS 103 b (stageSecondCoordinate stage) 0 r) _ at hfour
  rw [hbudget] at hfour
  have hbc : b 8 = 0 := (stage_four_budget_bank base stage reserve firstPadding padding nextPadding 0).1
  have hbn : b 3 = 0 := (stage_four_budget_bank base stage reserve firstPadding padding nextPadding 0).2
  have hstage : bankAS b 0 0 1 = stage := by
    simpa [bankAS] using stage_four_budget_bank_stage base stage reserve firstPadding padding nextPadding 0
  have hbudgetblock : graphSystem.Block (cfgAS 103 b 0 0 r) 2
      (cfgBudget 119 (bankAS b 0 0) 0 (b 5) 0 0 r) [] := by
    simpa [hbn] using emitted_coordinate_budget_success 0 0 b r hbc (by simpa using hbn)
  have hs : bankAS b 0 0 0 = 0 := by simp [bankAS]
  obtain ⟨tailDuration, tailPadding, ht, htail⟩ := budget_exit_count_zero_frame 0 (b 5) (bankAS b 0 0) r hs
  rw [hstage] at htail
  have h := (hfour.trans graphSystem hbudgetblock).trans graphSystem htail
  have hw : stageFourWord stage ++ [false] =
      PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
        (M236Game.selectedValue (Schedule.scheduledAddress stage)) := by
    rw [rank_two_selected_value_false stage hpositive]
    have hword := stage_overflow_address_word stage 0 hpos
    simp only [Schedule.decodeCoordinates, PASoundness.UnaryCodec.encodeFields, List.append_nil] at hword
    rw [hword, encode_fields_false_frame]
  simp only [List.append_nil] at h
  rw [hw] at h
  refine ⟨_, _, ?_, h⟩
  simp only [stageFourDuration, stageThreeDuration, thirdFieldDuration] at *
  omega

/-- Physical lift conditional on the actual selected run reaching the stated
clean rank-two scheduler entry. -/
theorem selected_scheduler_rank_two_bounded_frame (i stage : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = 1) (hbudget : stageSecondCoordinate stage = 0)
    (h : graphSystem.run i = cfg 0 base stage 0 0 reserve) :
    ∃ steps nextReserve finish, 0 < steps ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve ∧
      graphSystem.run (i+steps) = cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+steps)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+steps)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
            (M236Game.selectedValue (Schedule.scheduledAddress stage)) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+steps) := by
  obtain ⟨steps, nextReserve, ht, block⟩ :=
    scheduler_rank_two_bounded_frame stage base reserve ha hc hcount hpositive hbudget
  have hr : graphSystem.run (i+steps) = cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+steps) = graphSystem.prefixWord i ++
      PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
        (M236Game.selectedValue (Schedule.scheduledAddress stage)) := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i+steps)
  refine ⟨steps, nextReserve, finish, ht, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

/-- All rank-two stages are covered: a zero second coordinate takes the
bounded timeout, and a positive one takes the established overflow branch. -/
theorem scheduler_rank_two_frame (stage : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = 1) :
    ∃ steps nextReserve, 0 < steps ∧
      graphSystem.Block (cfg 0 base stage 0 0 reserve) steps
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve)
        (PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
          (M236Game.selectedValue (Schedule.scheduledAddress stage))) := by
  by_cases hq : stageSecondCoordinate stage = 0
  · exact scheduler_rank_two_bounded_frame stage base reserve ha hc hcount hpositive hq
  · have hextra : ∃ extra, stageSecondCoordinate stage = 0+extra+1 := by
      refine ⟨stageSecondCoordinate stage-1, ?_⟩
      omega
    obtain ⟨extra, hextra⟩ := hextra
    exact scheduler_overflow_frame stage 0 extra base reserve ha hc hcount (by simpa using hpositive) hextra

/-- Physical lift for any rank-two stage at a reached clean scheduler entry. -/
theorem selected_scheduler_rank_two_frame (i stage : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = 1)
    (h : graphSystem.run i = cfg 0 base stage 0 0 reserve) :
    ∃ steps nextReserve finish, 0 < steps ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve ∧
      graphSystem.run (i+steps) = cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+steps)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+steps)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
            (M236Game.selectedValue (Schedule.scheduledAddress stage)) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+steps) := by
  obtain ⟨steps, nextReserve, ht, block⟩ := scheduler_rank_two_frame stage base reserve ha hc hcount hpositive
  have hr : graphSystem.run (i+steps) = cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+steps) = graphSystem.prefixWord i ++
      PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
        (M236Game.selectedValue (Schedule.scheduledAddress stage)) := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i+steps)
  refine ⟨steps, nextReserve, finish, ht, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

/-- The selected blank-start run completes the first two scheduled frames and
reaches the clean stage-two graph boundary. This is a finite result. -/
theorem first_two_frames_on_selected :
    ∃ i steps reserve finish, 0 < steps ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros 2 0 0 reserve ∧
      graphSystem.run (i+steps) = cfg 0 BlankFirst.zeros 2 0 0 reserve ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+steps)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+steps)) =
        PASoundness.UnaryCodec.encodeFrame ⟨1, 0, [0]⟩ false ++
          PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress 1)
            (M236Game.selectedValue (Schedule.scheduledAddress 1)) := by
  obtain ⟨i, _, reserve, _, hgraph, _, _, hprefix⟩ := initial_frame_on_selected
  have hpositive : (Cantor.unpair 1).1 = 1 := by simp [Cantor.unpair, Cantor.unpairAux]
  obtain ⟨steps, nextReserve, finish, ht, hg, hs, hr, hconfig, hp, _⟩ :=
    selected_scheduler_rank_two_frame i 1 BlankFirst.zeros reserve rfl rfl rfl hpositive hgraph
  refine ⟨i, steps, nextReserve, finish, ht, hg, ?_, ?_, hconfig, ?_⟩
  · simpa using hs
  · simpa using hr
  · simpa [hprefix] using hp

/-- The actual selected run agrees with the repeated-address source through
two complete frames and reaches the clean stage-two graph entry. This finite
prefix equality is not an all-stage source refinement. -/
theorem first_two_source_frames_on_selected :
    ∃ i steps reserve finish, 0 < steps ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros 2 0 0 reserve ∧
      graphSystem.run (i+steps) = cfg 0 BlankFirst.zeros 2 0 0 reserve ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+steps)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+steps)) =
        (Source.source M236Game.selectedValue).prefixWord 2 := by
  obtain ⟨i, steps, reserve, finish, ht, hg, hs, hr, hconfig, hp⟩ := first_two_frames_on_selected
  have hframe0 : PASoundness.UnaryCodec.encodeFrame ⟨1, 0, [0]⟩ false =
      PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress 0)
        (M236Game.selectedValue (Schedule.scheduledAddress 0)) := by
    simp [Schedule.scheduledAddress, Schedule.decodeCoordinates, Cantor.unpair, Cantor.unpairAux,
      M236Game.selectedValue]
  have hsource : (Source.source M236Game.selectedValue).prefixWord 2 =
      PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress 0)
        (M236Game.selectedValue (Schedule.scheduledAddress 0)) ++
      PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress 1)
        (M236Game.selectedValue (Schedule.scheduledAddress 1)) := by
    simp [WordEventSystem.prefix_succ, Source.source]
  refine ⟨i, steps, reserve, finish, ht, hg, hs, hr, hconfig, ?_⟩
  rw [hframe0, ← hsource] at hp
  exact hp

end PASoundness.M236.OccurrenceGraph
