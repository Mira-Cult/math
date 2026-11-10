import PASoundness.M236StageFourFields

/-! Successful coordinate-budget scan and restoration on the checked graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def bankBudget (base : RegisterMachine.Bank 9) (count env a c : Nat) : RegisterMachine.Bank 9 :=
  fun i => if i = 3 then count else if i = 5 then env else if i = 6 then a else if i = 8 then c else base i

def cfgBudget (index : Nat) (base : RegisterMachine.Bank 9) (count env a c : Nat)
    (reserve : List Nat) : GraphState := ⟨index, bankBudget base count env a c, reserve⟩

theorem budget_row103 : sourceRows[103]? = some ("3.k.a.decnz", 104, some 114) := by decide
theorem budget_row104 : sourceRows[104]? = some ("3.k.count.decnz", 105, some 106) := by decide
theorem budget_row105 : sourceRows[105]? = some ("jump", 112, none) := by decide
theorem budget_row112 : sourceRows[112]? = some ("3.k.c.inc", 113, none) := by decide
theorem budget_row113 : sourceRows[113]? = some ("jump", 103, none) := by decide
theorem budget_row114 : sourceRows[114]? = some ("3.k.c.decnz", 115, some 119) := by decide
theorem budget_row115 : sourceRows[115]? = some ("3.k.count.inc", 116, none) := by decide
theorem budget_row116 : sourceRows[116]? = some ("3.k.a.inc", 117, none) := by decide
theorem budget_row117 : sourceRows[117]? = some ("3.k.env.inc", 118, none) := by decide
theorem budget_row118 : sourceRows[118]? = some ("jump", 114, none) := by decide

theorem budget_dec_a (base : RegisterMachine.Bank 9) (count env n c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 103 base count env (n+1) c reserve) =
      (cfgBudget 104 base count env n c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgBudget, budget_row103, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem budget_zero_a (base : RegisterMachine.Bank 9) (count env c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 103 base count env 0 c reserve) = (cfgBudget 114 base count env 0 c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, budget_row103, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute, RegisterMachine.write]

theorem budget_dec_count (base : RegisterMachine.Bank 9) (n env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 104 base (n+1) env a c reserve) =
      (cfgBudget 105 base n env a c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgBudget, budget_row104, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem budget_jump105 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 105 base count env a c reserve) = (cfgBudget 112 base count env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, budget_row105, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem budget_inc_c (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 112 base count env a c reserve) = (cfgBudget 113 base count env a (c+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, budget_row112, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem budget_jump113 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 113 base count env a c reserve) = (cfgBudget 103 base count env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, budget_row113, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem budget_dec_c (base : RegisterMachine.Bank 9) (count env a n : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 114 base count env a (n+1) reserve) =
      (cfgBudget 115 base count env a n (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgBudget, budget_row114, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem budget_zero_c (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 114 base count env a 0 reserve) = (cfgBudget 119 base count env a 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, budget_row114, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute, RegisterMachine.write]

theorem budget_inc_count (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 115 base count env a c reserve) = (cfgBudget 116 base (count+1) env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, budget_row115, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem budget_inc_a (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 116 base count env a c reserve) = (cfgBudget 117 base count env (a+1) c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, budget_row116, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem budget_inc_env (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 117 base count env a c reserve) = (cfgBudget 118 base count (env+1) a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, budget_row117, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem budget_jump118 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 118 base count env a c reserve) = (cfgBudget 114 base count env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, budget_row118, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem budget_consume_cycle (base : RegisterMachine.Bank 9) (count env n c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 103 base (count+1) env (n+1) c reserve) 5
      (cfgBudget 103 base count env n (c+1) ((reserve ++ [0]) ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (budget_dec_a base (count+1) env n c reserve)
  have h2 := WordEventSystem.Block.single graphSystem (budget_dec_count base count env n c (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (budget_jump105 base count env n c ((reserve ++ [0]) ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (budget_inc_c base count env n c ((reserve ++ [0]) ++ [0]))
  have h5 := WordEventSystem.Block.single graphSystem (budget_jump113 base count env n (c+1) ((reserve ++ [0]) ++ [0]))
  simpa using (((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5

theorem budget_consume_all (n : Nat) (base : RegisterMachine.Bank 9) (remaining env c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 103 base (remaining+n) env n c reserve) (5*n)
      (cfgBudget 103 base remaining env 0 (c+n) (reserve ++ List.replicate (2*n) 0)) [] := by
  induction n generalizing c reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgBudget 103 base remaining env 0 c reserve)
  | succ n ih =>
    have h := (budget_consume_cycle base (remaining+n) env n c reserve).trans graphSystem
      (ih (c+1) ((reserve ++ [0]) ++ [0]))
    have hres : ((reserve ++ [0]) ++ [0]) ++ List.replicate (2*n) 0 =
        reserve ++ List.replicate (2*(n+1)) 0 := by
      have ht : 2*(n+1) = 2 + 2*n := by omega
      rw [ht, List.replicate_add]
      simp [List.replicate_succ, List.append_assoc]
    rw [hres] at h
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem budget_restore_cycle (base : RegisterMachine.Bank 9) (count env a n : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 114 base count env a (n+1) reserve) 5
      (cfgBudget 114 base (count+1) (env+1) (a+1) n (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (budget_dec_c base count env a n reserve)
  have h2 := WordEventSystem.Block.single graphSystem (budget_inc_count base count env a n (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (budget_inc_a base (count+1) env a n (reserve ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (budget_inc_env base (count+1) env (a+1) n (reserve ++ [0]))
  have h5 := WordEventSystem.Block.single graphSystem (budget_jump118 base (count+1) (env+1) (a+1) n (reserve ++ [0]))
  simpa using (((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5

theorem budget_restore_all (n : Nat) (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 114 base count env a n reserve) (5*n)
      (cfgBudget 114 base (count+n) (env+n) (a+n) 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing count env a reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgBudget 114 base count env a 0 reserve)
  | succ n ih =>
    have h := (budget_restore_cycle base count env a n reserve).trans graphSystem
      (ih (count+1) (env+1) (a+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- If `a = n` and the counter is `remaining+n`, the successful scan restores
both, adds `n` to `env`, clears `c`, and reaches entry 119 silently. -/
theorem coordinate_budget_success (n : Nat) (base : RegisterMachine.Bank 9)
    (remaining env : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 103 base (remaining+n) env n 0 reserve) (10*n+2)
      (cfgBudget 119 base (remaining+n) (env+n) n 0
        ((reserve ++ List.replicate (2*n) 0) ++ List.replicate n 0)) [] := by
  have h1 := budget_consume_all n base remaining env 0 reserve
  have h2 := WordEventSystem.Block.single graphSystem
    (budget_zero_a base remaining env n (reserve ++ List.replicate (2*n) 0))
  have h3 := budget_restore_all n base remaining env 0 (reserve ++ List.replicate (2*n) 0)
  simp only [Nat.zero_add] at h1 h3
  have h4 := WordEventSystem.Block.single graphSystem
    (budget_zero_c base (remaining+n) (env+n) n
      ((reserve ++ List.replicate (2*n) 0) ++ List.replicate n 0))
  have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4
  have ht : 5*n+1+5*n+1 = 10*n+2 := by omega
  simpa [ht] using h

theorem emit_exit_to_budget (base : RegisterMachine.Bank 9) (n : Nat) (reserve : List Nat)
    (hc : base 8 = 0) :
    cfgAS 103 base n 0 reserve =
      cfgBudget 103 (bankAS base n 0) (base 3) (base 5) n 0 reserve := by
  unfold cfgAS cfgBudget
  congr 1
  funext i
  fin_cases i <;> simp [bankAS, bankBudget, hc]

/-- Successful budget processing directly from the prepared emitter exit. -/
theorem emitted_coordinate_budget_success (n remaining : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 = remaining+n) :
    graphSystem.Block (cfgAS 103 base n 0 reserve) (10*n+2)
      (cfgBudget 119 (bankAS base n 0) (base 3) (base 5+n) n 0
        ((reserve ++ List.replicate (2*n) 0) ++ List.replicate n 0)) [] := by
  rw [emit_exit_to_budget base n reserve hc, hcount]
  exact coordinate_budget_success n (bankAS base n 0) remaining (base 5) reserve

/-- Lift a successful budget block at an explicitly reached emitter exit. -/
theorem selected_emitted_coordinate_budget_success (i n remaining : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 = remaining+n)
    (h : graphSystem.run i = cfgAS 103 base n 0 reserve) :
    ∃ finish, Good finish ∧
      finish.graphState = cfgBudget 119 (bankAS base n 0) (base 3) (base 5+n) n 0
        ((reserve ++ List.replicate (2*n) 0) ++ List.replicate n 0) ∧
      graphSystem.run (i + (10*n+2)) = cfgBudget 119 (bankAS base n 0) (base 3) (base 5+n) n 0
        ((reserve ++ List.replicate (2*n) 0) ++ List.replicate n 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + (10*n+2))) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i + (10*n+2))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i + (10*n+2)) := by
  have block := emitted_coordinate_budget_success n remaining base reserve hc hcount
  have hr : graphSystem.run (i + (10*n+2)) = cfgBudget 119 (bankAS base n 0) (base 3) (base 5+n) n 0
      ((reserve ++ List.replicate (2*n) 0) ++ List.replicate n 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i + (10*n+2)) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i + (10*n+2))
  refine ⟨finish, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

def stageFourBudgetBank (base : RegisterMachine.Bank 9) (stage : Nat) (reserve : List Nat)
    (firstPadding padding nextPadding count : Nat) : RegisterMachine.Bank 9 :=
  bankAC (bankRest (stageFourthBase base stage reserve firstPadding padding nextPadding count)
    (Cantor.unpair (stageRemaining stage)).2) (stageSecondCoordinate stage) 0

def stageFourBudgetReserve (base : RegisterMachine.Bank 9) (stage : Nat) (reserve : List Nat)
    (firstPadding padding nextPadding fourthPadding : Nat) : List Nat :=
  ((stageFourthReserve base stage reserve firstPadding padding nextPadding ++ List.replicate fourthPadding 0) ++
    List.replicate (stageSecondCoordinate stage) 0) ++ List.replicate (stageSecondCoordinate stage) 0

theorem stage_four_budget_bank (base : RegisterMachine.Bank 9) (stage : Nat) (reserve : List Nat)
    (firstPadding padding nextPadding count : Nat) :
    stageFourBudgetBank base stage reserve firstPadding padding nextPadding count 8 = 0 ∧
      stageFourBudgetBank base stage reserve firstPadding padding nextPadding count 3 = count := by
  simp [stageFourBudgetBank, stageFourthBase, bankAC, bankRest, bankCountTop]

def stageBudgetExit (base : RegisterMachine.Bank 9) (stage : Nat) (reserve : List Nat)
    (firstPadding padding nextPadding count fourthPadding : Nat) : GraphState :=
  let b := stageFourBudgetBank base stage reserve firstPadding padding nextPadding count
  let q := stageSecondCoordinate stage
  let r := stageFourBudgetReserve base stage reserve firstPadding padding nextPadding fourthPadding
  cfgBudget 119 (bankAS b q 0) (b 3) (b 5+q) q 0
    ((r ++ List.replicate (2*q) 0) ++ List.replicate q 0)

def stageBudgetDuration (base : RegisterMachine.Bank 9)
    (stage firstDuration duration nextDuration fourthDuration : Nat) : Nat :=
  stageFourDuration base stage firstDuration duration nextDuration fourthDuration +
    (10*stageSecondCoordinate stage+2)

/-- For a stage with a second coordinate within the remaining counter, the
four scheduled fields continue through the successful budget routine. -/
theorem scheduler_four_fields_budget_success (stage count : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = count+1) (hbudget : stageSecondCoordinate stage ≤ count) :
    ∃ firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration fourthPadding,
      stage+1 ≤ firstDuration ∧ (Cantor.unpair stage).2+1 ≤ duration ∧
      (Cantor.unpair (Cantor.unpair stage).2).2+1 ≤ nextDuration ∧ stageRemaining stage+1 ≤ fourthDuration ∧
      graphSystem.Block (cfg 0 base stage 0 0 reserve)
        (stageBudgetDuration base stage firstDuration duration nextDuration fourthDuration)
        (stageBudgetExit base stage reserve firstPadding padding nextPadding count fourthPadding)
        (stageFourWord stage) := by
  obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    hf, hd, hn, hfourth, block⟩ := scheduler_first_four_fields stage count base reserve ha hc hcount hpositive
  change graphSystem.Block (cfg 0 base stage 0 0 reserve) _
    (cfgAS 103 (stageFourBudgetBank base stage reserve firstPadding padding nextPadding count)
      (stageSecondCoordinate stage) 0
      (stageFourBudgetReserve base stage reserve firstPadding padding nextPadding fourthPadding)) _ at block
  obtain ⟨hc', hcount'⟩ := stage_four_budget_bank base stage reserve firstPadding padding nextPadding count
  have hsum : stageFourBudgetBank base stage reserve firstPadding padding nextPadding count 3 =
      (count - stageSecondCoordinate stage) + stageSecondCoordinate stage := by
    rw [hcount']
    exact (Nat.sub_add_cancel hbudget).symm
  have hbudgetBlock := emitted_coordinate_budget_success (stageSecondCoordinate stage)
    (count - stageSecondCoordinate stage) (stageFourBudgetBank base stage reserve firstPadding padding nextPadding count)
    (stageFourBudgetReserve base stage reserve firstPadding padding nextPadding fourthPadding) hc' hsum
  refine ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    hf, hd, hn, hfourth, ?_⟩
  simpa [stageBudgetDuration, stageBudgetExit] using block.trans graphSystem hbudgetBlock

/-- The successful composed budget block on the literal selected run at an
explicitly reached clean scheduler entry. -/
theorem selected_scheduler_four_fields_budget_success (i stage count : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (ha : base 6 = 0) (hc : base 8 = 0) (hcount : base 3 = 0)
    (hpositive : (Cantor.unpair stage).1 = count+1) (hbudget : stageSecondCoordinate stage ≤ count)
    (h : graphSystem.run i = cfg 0 base stage 0 0 reserve) :
    ∃ firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration fourthPadding finish,
      stage+1 ≤ firstDuration ∧ (Cantor.unpair stage).2+1 ≤ duration ∧
      (Cantor.unpair (Cantor.unpair stage).2).2+1 ≤ nextDuration ∧ stageRemaining stage+1 ≤ fourthDuration ∧
      Good finish ∧
      finish.graphState = stageBudgetExit base stage reserve firstPadding padding nextPadding count fourthPadding ∧
      graphSystem.run (i + stageBudgetDuration base stage firstDuration duration nextDuration fourthDuration) =
        stageBudgetExit base stage reserve firstPadding padding nextPadding count fourthPadding ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + stageBudgetDuration base stage firstDuration duration nextDuration fourthDuration)) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary (i + stageBudgetDuration base stage firstDuration duration nextDuration fourthDuration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++ stageFourWord stage ∧
      graphRefinement.boundary i <
        graphRefinement.boundary (i + stageBudgetDuration base stage firstDuration duration nextDuration fourthDuration) := by
  obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    hf, hd, hn, hfourth, block⟩ :=
      scheduler_four_fields_budget_success stage count base reserve ha hc hcount hpositive hbudget
  have hr : graphSystem.run (i + stageBudgetDuration base stage firstDuration duration nextDuration fourthDuration) =
      stageBudgetExit base stage reserve firstPadding padding nextPadding count fourthPadding := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i + stageBudgetDuration base stage firstDuration duration nextDuration fourthDuration) =
      graphSystem.prefixWord i ++ stageFourWord stage := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related
    (i + stageBudgetDuration base stage firstDuration duration nextDuration fourthDuration)
  refine ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    finish, hf, hd, hn, hfourth, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    simp only [stageBudgetDuration]
    omega

/-- The actual stage-one run satisfies the successful budget condition and
reaches entry 119 with no output beyond its first four scheduled fields. -/
theorem stage_one_budget_on_selected :
    ∃ i firstDuration firstPadding duration padding nextDuration nextPadding fourthDuration fourthPadding reserve finish,
      Good finish ∧
      graphSystem.run (i + stageBudgetDuration BlankFirst.zeros 1 firstDuration duration nextDuration fourthDuration) =
        stageBudgetExit BlankFirst.zeros 1 reserve firstPadding padding nextPadding 0 fourthPadding ∧
      finish.graphState = stageBudgetExit BlankFirst.zeros 1 reserve firstPadding padding nextPadding 0 fourthPadding ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + stageBudgetDuration BlankFirst.zeros 1 firstDuration duration nextDuration fourthDuration)) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary (i + stageBudgetDuration BlankFirst.zeros 1 firstDuration duration nextDuration fourthDuration)) =
        PASoundness.UnaryCodec.encodeFrame ⟨1, 0, [0]⟩ false ++ stageFourWord 1 := by
  obtain ⟨i, _, reserve, _, hstart, _, _, hpstart⟩ := initial_frame_on_selected
  have hpositive : (Cantor.unpair 1).1 = 0+1 := by simp [Cantor.unpair, Cantor.unpairAux]
  have hbudget : stageSecondCoordinate 1 ≤ 0 := by
    simp [stageSecondCoordinate, stageRemaining, Cantor.unpair, Cantor.unpairAux]
  obtain ⟨firstDuration, firstPadding, duration, padding, nextDuration, nextPadding, fourthDuration, fourthPadding,
    finish, _, _, _, _, hg, hs, hr, hconfig, hp, _⟩ :=
      selected_scheduler_four_fields_budget_success i 1 0 BlankFirst.zeros reserve rfl rfl rfl hpositive hbudget hstart
  refine ⟨i, firstDuration, firstPadding, duration, padding, nextDuration, nextPadding,
    fourthDuration, fourthPadding, reserve, finish, hg, hr, hs, hconfig, ?_⟩
  simpa [hpstart] using hp

end PASoundness.M236.OccurrenceGraph
