import PASoundness.M236CoordinateBudget

/-! The exceeding-budget branch of the checked coordinate scan. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

/-- Consume a prefix of `a` while retaining an arbitrary unconsumed tail. -/
theorem budget_consume_prefix (n : Nat) (base : RegisterMachine.Bank 9)
    (remaining extra env c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 103 base (remaining+n) env (extra+n) c reserve) (5*n)
      (cfgBudget 103 base remaining env extra (c+n) (reserve ++ List.replicate (2*n) 0)) [] := by
  induction n generalizing c reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgBudget 103 base remaining env extra c reserve)
  | succ n ih =>
    have h := (budget_consume_cycle base (remaining+n) env (extra+n) c reserve).trans graphSystem
      (ih (c+1) ((reserve ++ [0]) ++ [0]))
    have hres : ((reserve ++ [0]) ++ [0]) ++ List.replicate (2*n) 0 =
        reserve ++ List.replicate (2*(n+1)) 0 := by
      have ht : 2*(n+1) = 2 + 2*n := by omega
      rw [ht, List.replicate_add]
      simp [List.replicate_succ, List.append_assoc]
    rw [hres] at h
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem overflow_row106 : sourceRows[106]? = some ("3.k.c.decnz", 107, some 109) := by decide
theorem overflow_row107 : sourceRows[107]? = some ("3.k.count.inc", 108, none) := by decide
theorem overflow_row108 : sourceRows[108]? = some ("jump", 106, none) := by decide
theorem overflow_row109 : sourceRows[109]? = some ("3.k.top.decnz", 110, some 111) := by decide
theorem overflow_row110 : sourceRows[110]? = some ("jump", 109, none) := by decide
theorem overflow_row111 : sourceRows[111]? = some ("jump", 724, none) := by decide

theorem overflow_zero_count (base : RegisterMachine.Bank 9) (env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 104 base 0 env a c reserve) = (cfgBudget 106 base 0 env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, budget_row104, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute, RegisterMachine.write]

theorem overflow_dec_c (base : RegisterMachine.Bank 9) (count env a n : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 106 base count env a (n+1) reserve) =
      (cfgBudget 107 base count env a n (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgBudget, overflow_row106, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem overflow_zero_c (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 106 base count env a 0 reserve) = (cfgBudget 109 base count env a 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, overflow_row106, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute, RegisterMachine.write]

theorem overflow_inc_count (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 107 base count env a c reserve) = (cfgBudget 108 base (count+1) env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, overflow_row107, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem overflow_jump108 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 108 base count env a c reserve) = (cfgBudget 106 base count env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, overflow_row108, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem overflow_restore_cycle (base : RegisterMachine.Bank 9) (count env a n : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 106 base count env a (n+1) reserve) 3
      (cfgBudget 106 base (count+1) env a n (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (overflow_dec_c base count env a n reserve)
  have h2 := WordEventSystem.Block.single graphSystem (overflow_inc_count base count env a n (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (overflow_jump108 base (count+1) env a n (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem overflow_restore_all (n : Nat) (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 106 base count env a n reserve) (3*n)
      (cfgBudget 106 base (count+n) env a 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing count reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgBudget 106 base count env a 0 reserve)
  | succ n ih =>
    have h := (overflow_restore_cycle base count env a n reserve).trans graphSystem (ih (count+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

def bankBudgetTop (base : RegisterMachine.Bank 9) (count env a c top : Nat) : RegisterMachine.Bank 9 :=
  bankBudget (RegisterMachine.write base 4 top) count env a c

def cfgBudgetTop (index : Nat) (base : RegisterMachine.Bank 9) (count env a c top : Nat)
    (reserve : List Nat) : GraphState := ⟨index, bankBudgetTop base count env a c top, reserve⟩

theorem budget_to_top_view (index : Nat) (base : RegisterMachine.Bank 9) (count env a c : Nat)
    (reserve : List Nat) : cfgBudget index base count env a c reserve =
      cfgBudgetTop index base count env a c (base 4) reserve := by
  unfold cfgBudget cfgBudgetTop
  congr 1
  funext i
  fin_cases i <;> simp [bankBudgetTop, bankBudget, RegisterMachine.write]

theorem overflow_dec_top (base : RegisterMachine.Bank 9) (count env a c n : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudgetTop 109 base count env a c (n+1) reserve) =
      (cfgBudgetTop 110 base count env a c n (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgBudgetTop, overflow_row109, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudgetTop, bankBudget, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankBudgetTop, bankBudget, RegisterMachine.write])

theorem overflow_zero_top (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudgetTop 109 base count env a c 0 reserve) = (cfgBudgetTop 111 base count env a c 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgBudgetTop, overflow_row109, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudgetTop, bankBudget, RegisterMachine.execute, RegisterMachine.write]

theorem overflow_jump110 (base : RegisterMachine.Bank 9) (count env a c top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudgetTop 110 base count env a c top reserve) = (cfgBudgetTop 109 base count env a c top reserve, []) := by
  simp [graphSystem, graphNext, cfgBudgetTop, overflow_row110, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem overflow_jump111 (base : RegisterMachine.Bank 9) (count env a c top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudgetTop 111 base count env a c top reserve) = (cfgBudgetTop 724 base count env a c top reserve, []) := by
  simp [graphSystem, graphNext, cfgBudgetTop, overflow_row111, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem overflow_drain_top (n : Nat) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudgetTop 109 base count env a c n reserve) (2*n)
      (cfgBudgetTop 109 base count env a c 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgBudgetTop 109 base count env a c 0 reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (overflow_dec_top base count env a c n reserve)
    have h2 := WordEventSystem.Block.single graphSystem (overflow_jump110 base count env a c n (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- When `a = count+extra+1`, the scan exhausts the counter, restores it,
drains `top`, and returns to cleanup with `a = extra`. -/
theorem coordinate_budget_overflow (count extra : Nat) (base : RegisterMachine.Bank 9)
    (env : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 103 base count env (count+extra+1) 0 reserve)
      (8*count + 2*(base 4) + 5)
      (cfgBudgetTop 724 base count env extra 0 0
        ((((reserve ++ List.replicate (2*count) 0) ++ [0]) ++ List.replicate count 0) ++
          List.replicate (base 4) 0)) [] := by
  have h1 : graphSystem.Block (cfgBudget 103 base count env (count+extra+1) 0 reserve) (5*count)
      (cfgBudget 103 base 0 env (extra+1) count (reserve ++ List.replicate (2*count) 0)) [] := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      budget_consume_prefix count base 0 (extra+1) env 0 reserve
  have h2 := WordEventSystem.Block.single graphSystem
    (budget_dec_a base 0 env extra count (reserve ++ List.replicate (2*count) 0))
  have h3 := WordEventSystem.Block.single graphSystem
    (overflow_zero_count base env extra count ((reserve ++ List.replicate (2*count) 0) ++ [0]))
  have h4 := overflow_restore_all count base 0 env extra ((reserve ++ List.replicate (2*count) 0) ++ [0])
  simp only [Nat.zero_add] at h4
  have h5 := WordEventSystem.Block.single graphSystem
    (overflow_zero_c base count env extra (((reserve ++ List.replicate (2*count) 0) ++ [0]) ++ List.replicate count 0))
  rw [budget_to_top_view 109 base count env extra 0
    (((reserve ++ List.replicate (2*count) 0) ++ [0]) ++ List.replicate count 0)] at h5
  have h6 := overflow_drain_top (base 4) base count env extra 0
    (((reserve ++ List.replicate (2*count) 0) ++ [0]) ++ List.replicate count 0)
  have h7 := WordEventSystem.Block.single graphSystem
    (overflow_zero_top base count env extra 0
      ((((reserve ++ List.replicate (2*count) 0) ++ [0]) ++ List.replicate count 0) ++ List.replicate (base 4) 0))
  have h8 := WordEventSystem.Block.single graphSystem
    (overflow_jump111 base count env extra 0 0
      ((((reserve ++ List.replicate (2*count) 0) ++ [0]) ++ List.replicate count 0) ++ List.replicate (base 4) 0))
  have h := ((((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5).trans graphSystem h6).trans graphSystem h7).trans graphSystem h8
  have ht : 5*count+1+1+3*count+1+2*(base 4)+1+1 = 8*count+2*(base 4)+5 := by omega
  simpa [ht] using h

/-- Overflow behavior directly from a prepared emitter exit. -/
theorem emitted_coordinate_budget_overflow (count extra : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 = count) :
    graphSystem.Block (cfgAS 103 base (count+extra+1) 0 reserve) (8*count+2*(base 4)+5)
      (cfgBudgetTop 724 (bankAS base (count+extra+1) 0) count (base 5) extra 0 0
        ((((reserve ++ List.replicate (2*count) 0) ++ [0]) ++ List.replicate count 0) ++
          List.replicate (base 4) 0)) [] := by
  rw [emit_exit_to_budget base (count+extra+1) reserve hc, hcount]
  simpa [bankAS] using coordinate_budget_overflow count extra (bankAS base (count+extra+1) 0) (base 5) reserve

/-- Physical lift of the overflow path at a reached emitter exit. -/
theorem selected_emitted_coordinate_budget_overflow (i count extra : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 = count)
    (h : graphSystem.run i = cfgAS 103 base (count+extra+1) 0 reserve) :
    ∃ finish, Good finish ∧
      finish.graphState = cfgBudgetTop 724 (bankAS base (count+extra+1) 0) count (base 5) extra 0 0
        ((((reserve ++ List.replicate (2*count) 0) ++ [0]) ++ List.replicate count 0) ++ List.replicate (base 4) 0) ∧
      graphSystem.run (i + (8*count+2*(base 4)+5)) =
        cfgBudgetTop 724 (bankAS base (count+extra+1) 0) count (base 5) extra 0 0
          ((((reserve ++ List.replicate (2*count) 0) ++ [0]) ++ List.replicate count 0) ++ List.replicate (base 4) 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + (8*count+2*(base 4)+5))) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i + (8*count+2*(base 4)+5))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i + (8*count+2*(base 4)+5)) := by
  have block := emitted_coordinate_budget_overflow count extra base reserve hc hcount
  have hr : graphSystem.run (i + (8*count+2*(base 4)+5)) =
      cfgBudgetTop 724 (bankAS base (count+extra+1) 0) count (base 5) extra 0 0
        ((((reserve ++ List.replicate (2*count) 0) ++ [0]) ++ List.replicate count 0) ++ List.replicate (base 4) 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i + (8*count+2*(base 4)+5)) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i + (8*count+2*(base 4)+5))
  refine ⟨finish, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

def stageOverflowDuration (base : RegisterMachine.Bank 9) (stage : Nat) (reserve : List Nat)
    (firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration count : Nat) : Nat :=
  stageFourDuration base stage firstDuration duration nextDuration fourthDuration +
    (8*count + 2*(stageFourBudgetBank base stage reserve firstPadding padding nextPadding count 4) + 5)

def stageOverflowExit (base : RegisterMachine.Bank 9) (stage : Nat) (reserve : List Nat)
    (firstPadding padding nextPadding count fourthPadding extra : Nat) : GraphState :=
  let b := stageFourBudgetBank base stage reserve firstPadding padding nextPadding count
  let r := stageFourBudgetReserve base stage reserve firstPadding padding nextPadding fourthPadding
  cfgBudgetTop 724 (bankAS b (stageSecondCoordinate stage) 0) count (b 5) extra 0 0
    ((((r ++ List.replicate (2*count) 0) ++ [0]) ++ List.replicate count 0) ++ List.replicate (b 4) 0)

/-- For a rank-at-least-two stage whose second coordinate exceeds its counter,
the four-field block follows the checked overflow path to cleanup. -/
theorem scheduler_four_fields_budget_overflow (stage count extra : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = count+1)
    (hoverflow : stageSecondCoordinate stage = count+extra+1) :
    ∃ firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration fourthPadding,
      stage+1 ≤ firstDuration ∧ (Cantor.unpair stage).2+1 ≤ duration ∧
      (Cantor.unpair (Cantor.unpair stage).2).2+1 ≤ nextDuration ∧ stageRemaining stage+1 ≤ fourthDuration ∧
      graphSystem.Block (cfg 0 base stage 0 0 reserve)
        (stageOverflowDuration base stage reserve firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration count)
        (stageOverflowExit base stage reserve firstPadding padding nextPadding count fourthPadding extra)
        (stageFourWord stage) := by
  obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    hf, hd, hn, hfourth, block⟩ := scheduler_first_four_fields stage count base reserve ha hc hcount hpositive
  change graphSystem.Block (cfg 0 base stage 0 0 reserve) _
    (cfgAS 103 (stageFourBudgetBank base stage reserve firstPadding padding nextPadding count)
      (stageSecondCoordinate stage) 0
      (stageFourBudgetReserve base stage reserve firstPadding padding nextPadding fourthPadding)) _ at block
  obtain ⟨hc', hcount'⟩ := stage_four_budget_bank base stage reserve firstPadding padding nextPadding count
  have hover := emitted_coordinate_budget_overflow count extra
    (stageFourBudgetBank base stage reserve firstPadding padding nextPadding count)
    (stageFourBudgetReserve base stage reserve firstPadding padding nextPadding fourthPadding) hc' hcount'
  rw [← hoverflow] at hover
  refine ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    hf, hd, hn, hfourth, ?_⟩
  simpa [stageOverflowDuration, stageOverflowExit] using block.trans graphSystem hover

/-- The composed overflow block lifts to the selected literal execution at an
explicitly reached clean scheduler entry. -/
theorem selected_scheduler_four_fields_budget_overflow (i stage count extra : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = count+1)
    (hoverflow : stageSecondCoordinate stage = count+extra+1)
    (h : graphSystem.run i = cfg 0 base stage 0 0 reserve) :
    ∃ firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration fourthPadding finish,
      stage+1 ≤ firstDuration ∧ (Cantor.unpair stage).2+1 ≤ duration ∧
      (Cantor.unpair (Cantor.unpair stage).2).2+1 ≤ nextDuration ∧ stageRemaining stage+1 ≤ fourthDuration ∧
      Good finish ∧
      finish.graphState = stageOverflowExit base stage reserve firstPadding padding nextPadding count fourthPadding extra ∧
      graphSystem.run (i + stageOverflowDuration base stage reserve firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration count) =
        stageOverflowExit base stage reserve firstPadding padding nextPadding count fourthPadding extra ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + stageOverflowDuration base stage reserve firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration count)) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary (i + stageOverflowDuration base stage reserve firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration count)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++ stageFourWord stage ∧
      graphRefinement.boundary i < graphRefinement.boundary
        (i + stageOverflowDuration base stage reserve firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration count) := by
  obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    hf, hd, hn, hfourth, block⟩ :=
      scheduler_four_fields_budget_overflow stage count extra base reserve ha hc hcount hpositive hoverflow
  have hr : graphSystem.run
      (i + stageOverflowDuration base stage reserve firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration count) =
      stageOverflowExit base stage reserve firstPadding padding nextPadding count fourthPadding extra := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord
      (i + stageOverflowDuration base stage reserve firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration count) =
      graphSystem.prefixWord i ++ stageFourWord stage := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related
    (i + stageOverflowDuration base stage reserve firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration count)
  refine ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    finish, hf, hd, hn, hfourth, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    simp only [stageOverflowDuration]
    omega

/-- The successful and overflow cases exhaust all coordinates. Their detailed
theorems retain the complete endpoint states and precise durations. -/
theorem scheduler_four_fields_budget_dispatch (stage count : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = count+1) :
    ∃ steps final, 0 < steps ∧
      graphSystem.Block (cfg 0 base stage 0 0 reserve) steps final (stageFourWord stage) ∧
      (final.index = 119 ∨ final.index = 724) := by
  by_cases hbudget : stageSecondCoordinate stage ≤ count
  · obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
      _, _, _, _, block⟩ := scheduler_four_fields_budget_success stage count base reserve ha hc hcount hpositive hbudget
    refine ⟨stageBudgetDuration base stage firstDuration duration nextDuration fourthDuration,
      stageBudgetExit base stage reserve firstPadding padding nextPadding count fourthPadding, ?_, block, ?_⟩
    · simp only [stageBudgetDuration]; omega
    · left; rfl
  · have hextra : ∃ extra, stageSecondCoordinate stage = count+extra+1 := by
      refine ⟨stageSecondCoordinate stage - count - 1, ?_⟩
      omega
    obtain ⟨extra, hoverflow⟩ := hextra
    obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
      _, _, _, _, block⟩ := scheduler_four_fields_budget_overflow stage count extra base reserve ha hc hcount hpositive hoverflow
    refine ⟨stageOverflowDuration base stage reserve firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration count,
      stageOverflowExit base stage reserve firstPadding padding nextPadding count fourthPadding extra, ?_, block, ?_⟩
    · simp only [stageOverflowDuration]; omega
    · right; rfl

/-- The exhaustive dispatch transfers to the selected machine at any reached
clean scheduler entry, preserving the exact four-field prefix. -/
theorem selected_scheduler_four_fields_budget_dispatch (i stage count : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = count+1)
    (h : graphSystem.run i = cfg 0 base stage 0 0 reserve) :
    ∃ steps finish, 0 < steps ∧ Good finish ∧ (finish.graphState.index = 119 ∨ finish.graphState.index = 724) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+steps)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+steps)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++ stageFourWord stage ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+steps) := by
  obtain ⟨steps, final, ht, block, hindex⟩ :=
    scheduler_four_fields_budget_dispatch stage count base reserve ha hc hcount hpositive
  have hr : graphSystem.run (i+steps) = final := by rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+steps) = graphSystem.prefixWord i ++ stageFourWord stage := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i+steps)
  refine ⟨steps, finish, ht, hg, ?_, hconfig, ?_, ?_⟩
  · rw [hs, hr]; exact hindex
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
