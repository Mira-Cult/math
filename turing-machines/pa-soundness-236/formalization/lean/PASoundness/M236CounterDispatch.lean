import PASoundness.M236FieldBranch

/-! Counter dispatch and finite top-register cleanup at two checked sites. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

structure CounterDispatchRows (k : Nat) : Prop where
  countDec : sourceRows[k]? = some ("3.k.count.decnz", k+1, some (k+2))
  nextJump : sourceRows[k+1]? = some ("jump", k+5, none)
  topDec : sourceRows[k+2]? = some ("3.k.top.decnz", k+3, some (k+4))
  drainJump : sourceRows[k+3]? = some ("jump", k+2, none)
  cleanupJump : sourceRows[k+4]? = some ("jump", 724, none)

theorem counter_dispatch_rows_52 : CounterDispatchRows 52 := by constructor <;> decide
theorem counter_dispatch_rows_79 : CounterDispatchRows 79 := by constructor <;> decide

def bankCountTop (base : RegisterMachine.Bank 9) (count top : Nat) : RegisterMachine.Bank 9 :=
  fun i => if i = 3 then count else if i = 4 then top else base i

def cfgCountTop (index : Nat) (base : RegisterMachine.Bank 9) (count top : Nat)
    (reserve : List Nat) : GraphState := ⟨index, bankCountTop base count top, reserve⟩

theorem dispatch_count_positive (k : Nat) (rows : CounterDispatchRows k)
    (base : RegisterMachine.Bank 9) (n top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgCountTop k base (n+1) top reserve) =
      (cfgCountTop (k+1) base n top (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgCountTop, rows.countDec, nextIndex, nextBank,
    nextReserve, incRegister, decRegister, outputForOp, bankCountTop,
    RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankCountTop, RegisterMachine.write])

theorem dispatch_count_zero (k : Nat) (rows : CounterDispatchRows k)
    (base : RegisterMachine.Bank 9) (top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgCountTop k base 0 top reserve) =
      (cfgCountTop (k+2) base 0 top reserve, []) := by
  simp [graphSystem, graphNext, cfgCountTop, rows.countDec, nextIndex, nextBank,
    nextReserve, incRegister, decRegister, outputForOp, bankCountTop,
    RegisterMachine.execute, RegisterMachine.write]

theorem dispatch_next_jump (k : Nat) (rows : CounterDispatchRows k)
    (base : RegisterMachine.Bank 9) (count top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgCountTop (k+1) base count top reserve) =
      (cfgCountTop (k+5) base count top reserve, []) := by
  simp [graphSystem, graphNext, cfgCountTop, rows.nextJump, nextIndex, nextBank,
    nextReserve, incRegister, decRegister, outputForOp]

theorem dispatch_top_positive (k : Nat) (rows : CounterDispatchRows k)
    (base : RegisterMachine.Bank 9) (count n : Nat) (reserve : List Nat) :
    graphSystem.step (cfgCountTop (k+2) base count (n+1) reserve) =
      (cfgCountTop (k+3) base count n (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgCountTop, rows.topDec, nextIndex, nextBank,
    nextReserve, incRegister, decRegister, outputForOp, bankCountTop,
    RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankCountTop, RegisterMachine.write])

theorem dispatch_top_zero (k : Nat) (rows : CounterDispatchRows k)
    (base : RegisterMachine.Bank 9) (count : Nat) (reserve : List Nat) :
    graphSystem.step (cfgCountTop (k+2) base count 0 reserve) =
      (cfgCountTop (k+4) base count 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgCountTop, rows.topDec, nextIndex, nextBank,
    nextReserve, incRegister, decRegister, outputForOp, bankCountTop,
    RegisterMachine.execute, RegisterMachine.write]

theorem dispatch_drain_jump (k : Nat) (rows : CounterDispatchRows k)
    (base : RegisterMachine.Bank 9) (count top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgCountTop (k+3) base count top reserve) =
      (cfgCountTop (k+2) base count top reserve, []) := by
  simp [graphSystem, graphNext, cfgCountTop, rows.drainJump, nextIndex, nextBank,
    nextReserve, incRegister, decRegister, outputForOp]

theorem dispatch_cleanup_jump (k : Nat) (rows : CounterDispatchRows k)
    (base : RegisterMachine.Bank 9) (count top : Nat) (reserve : List Nat) :
    graphSystem.step (cfgCountTop (k+4) base count top reserve) =
      (cfgCountTop 724 base count top reserve, []) := by
  simp [graphSystem, graphNext, cfgCountTop, rows.cleanupJump, nextIndex, nextBank,
    nextReserve, incRegister, decRegister, outputForOp]

theorem counter_dispatch_positive (k : Nat) (rows : CounterDispatchRows k)
    (base : RegisterMachine.Bank 9) (n top : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgCountTop k base (n+1) top reserve) 2
      (cfgCountTop (k+5) base n top (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (dispatch_count_positive k rows base n top reserve)
  have h2 := WordEventSystem.Block.single graphSystem (dispatch_next_jump k rows base n top (reserve ++ [0]))
  simpa using h1.trans graphSystem h2

theorem dispatch_drain_all (n k : Nat) (rows : CounterDispatchRows k)
    (base : RegisterMachine.Bank 9) (count : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgCountTop (k+2) base count n reserve) (2*n)
      (cfgCountTop (k+2) base count 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgCountTop (k+2) base count 0 reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (dispatch_top_positive k rows base count n reserve)
    have h2 := WordEventSystem.Block.single graphSystem (dispatch_drain_jump k rows base count n (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- With a zero counter, the finite top register is drained before cleanup. -/
theorem counter_dispatch_zero (n k : Nat) (rows : CounterDispatchRows k)
    (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    graphSystem.Block (cfgCountTop k base 0 n reserve) (2*n+3)
      (cfgCountTop 724 base 0 0 (reserve ++ List.replicate n 0)) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (dispatch_count_zero k rows base n reserve)
  have h2 := dispatch_drain_all n k rows base 0 reserve
  have h3 := WordEventSystem.Block.single graphSystem
    (dispatch_top_zero k rows base 0 (reserve ++ List.replicate n 0))
  have h4 := WordEventSystem.Block.single graphSystem
    (dispatch_cleanup_jump k rows base 0 0 (reserve ++ List.replicate n 0))
  have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4
  have ht : 1 + 2*n + 1 + 1 = 2*n+3 := by omega
  simpa [ht] using h

theorem cfg_count_top_self (k : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    cfgCountTop k base (base 3) (base 4) reserve = ⟨k, base, reserve⟩ := by
  unfold cfgCountTop
  congr 1
  funext i
  by_cases h3 : i = 3
  · subst i; simp [bankCountTop]
  · by_cases h4 : i = 4
    · subst i; simp [bankCountTop]
    · simp [bankCountTop, h3, h4]

theorem third_exit_count (base : RegisterMachine.Bank 9) (rank : Nat) (reserve : List Nat)
    (padding count nextPadding : Nat) :
    (thirdFieldExit base rank reserve padding count nextPadding).registers 3 = count := by
  simp [thirdFieldExit, cfgFieldTransfer, bankFieldTransfer, bankAS, thirdFieldBank,
    bankAC, bankRest, bankOnlyCount]

theorem third_exit_to_count_top (base : RegisterMachine.Bank 9) (rank : Nat) (reserve : List Nat)
    (padding count nextPadding : Nat) :
    thirdFieldExit base rank reserve padding count nextPadding =
      cfgCountTop 79 (thirdFieldExit base rank reserve padding count nextPadding).registers count
        ((thirdFieldExit base rank reserve padding count nextPadding).registers 4)
        (thirdFieldExit base rank reserve padding count nextPadding).reserve := by
  have h := cfg_count_top_self 79
    (thirdFieldExit base rank reserve padding count nextPadding).registers
    (thirdFieldExit base rank reserve padding count nextPadding).reserve
  rw [third_exit_count base rank reserve padding count nextPadding] at h
  exact h.symm

/-- If the counter is exhausted after the third field, the same graph block
continues silently through top cleanup to entry 724. -/
theorem rank_third_field_zero_cleanup (rank : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 + rank = 1) :
    ∃ duration padding nextDuration nextPadding,
      base 2 + 1 ≤ duration ∧ (Cantor.unpair (base 2)).2 + 1 ≤ nextDuration ∧
      graphSystem.Block (cfgAS 19 base rank 0 reserve)
        (thirdFieldDuration base rank duration nextDuration +
          (2*(thirdFieldExit base rank reserve padding 0 nextPadding).registers 4+3))
        (cfgCountTop 724 (thirdFieldExit base rank reserve padding 0 nextPadding).registers 0 0
          ((thirdFieldExit base rank reserve padding 0 nextPadding).reserve ++
            List.replicate ((thirdFieldExit base rank reserve padding 0 nextPadding).registers 4) 0))
        ((PASoundness.UnaryCodec.unary rank ++
          PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) ++
            PASoundness.UnaryCodec.unary (thirdFieldValue base)) := by
  obtain ⟨duration, padding, nextDuration, nextPadding, ht, hn, block⟩ :=
    rank_through_third_field rank 0 base reserve hc (by simpa using hcount)
  change graphSystem.Block (cfgAS 19 base rank 0 reserve)
    (thirdFieldDuration base rank duration nextDuration)
    (thirdFieldExit base rank reserve padding 0 nextPadding) _ at block
  rw [third_exit_to_count_top base rank reserve padding 0 nextPadding] at block
  have hclean := counter_dispatch_zero
    ((thirdFieldExit base rank reserve padding 0 nextPadding).registers 4) 79
    counter_dispatch_rows_79 (thirdFieldExit base rank reserve padding 0 nextPadding).registers
    (thirdFieldExit base rank reserve padding 0 nextPadding).reserve
  refine ⟨duration, padding, nextDuration, nextPadding, ht, hn, ?_⟩
  simpa using block.trans graphSystem hclean

def thirdCleanupDuration (base : RegisterMachine.Bank 9) (rank : Nat) (reserve : List Nat)
    (duration padding nextDuration nextPadding : Nat) : Nat :=
  thirdFieldDuration base rank duration nextDuration +
    (2*(thirdFieldExit base rank reserve padding 0 nextPadding).registers 4+3)

def thirdCleanupState (base : RegisterMachine.Bank 9) (rank : Nat) (reserve : List Nat)
    (padding nextPadding : Nat) : GraphState :=
  cfgCountTop 724 (thirdFieldExit base rank reserve padding 0 nextPadding).registers 0 0
    ((thirdFieldExit base rank reserve padding 0 nextPadding).reserve ++
      List.replicate ((thirdFieldExit base rank reserve padding 0 nextPadding).registers 4) 0)

/-- Physical lift of the exhausted-counter cleanup, conditional on the
prepared rank boundary occurring on the selected blank-start run. -/
theorem selected_rank_third_field_zero_cleanup (i rank : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) (hcount : base 3 + rank = 1)
    (h : graphSystem.run i = cfgAS 19 base rank 0 reserve) :
    ∃ duration padding nextDuration nextPadding finish,
      base 2 + 1 ≤ duration ∧ (Cantor.unpair (base 2)).2 + 1 ≤ nextDuration ∧ Good finish ∧
      finish.graphState = thirdCleanupState base rank reserve padding nextPadding ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + thirdCleanupDuration base rank reserve duration padding nextDuration nextPadding)) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary (i + thirdCleanupDuration base rank reserve duration padding nextDuration nextPadding)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          ((PASoundness.UnaryCodec.unary rank ++
            PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) ++
              PASoundness.UnaryCodec.unary (thirdFieldValue base)) ∧
      graphRefinement.boundary i <
        graphRefinement.boundary (i + thirdCleanupDuration base rank reserve duration padding nextDuration nextPadding) := by
  obtain ⟨duration, padding, nextDuration, nextPadding, ht, hn, block⟩ :=
    rank_third_field_zero_cleanup rank base reserve hc hcount
  change graphSystem.Block (cfgAS 19 base rank 0 reserve)
    (thirdCleanupDuration base rank reserve duration padding nextDuration nextPadding)
    (thirdCleanupState base rank reserve padding nextPadding) _ at block
  have hr := block.endpoint
  have hp := block.output
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related
    (i + thirdCleanupDuration base rank reserve duration padding nextDuration nextPadding)
  refine ⟨duration, padding, nextDuration, nextPadding, finish, ht, hn, hg, ?_, hconfig, ?_, ?_⟩
  · rw [WordEventSystem.run_add, h, hr] at hs
    exact hs
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, WordEventSystem.prefix_add, h, hp]
  · apply graphRefinement.boundary_strict
    simp only [thirdCleanupDuration]
    omega

/-- The actual blank-start run reaches the exhausted-counter cleanup after
the first three unary fields, with the exact finite output prefix. -/
theorem initial_third_field_cleanup_on_selected :
    ∃ t finish, Good finish ∧ finish.graphState.index = 724 ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run t ∧
      (machineWordSystem machine machineLabels).prefixWord t = [true, false, false, false] := by
  obtain ⟨before, padding, ht, scan⟩ := unpair_to_rank_entry 0 BlankFirst.zeros BlankFirst.reserve
  have hgraph : graphSystem.run (2 + before) =
      cfgAS 19 (rankBase BlankFirst.zeros 0 1) 1 0
        (BlankFirst.reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, initial_diagonal_entry, scan.endpoint]
    simpa [Cantor.unpair, Cantor.unpairAux] using
      rank_entry_convert BlankFirst.zeros 0 1
        (BlankFirst.reserve ++ List.replicate padding 0) rfl
  have hp2 : graphSystem.prefixWord 2 = [] := by
    have hg := (copy_at_graph_run 0 0 BlankFirst.zeros 0 BlankFirst.reserve initial_copy_entry).2
    simpa using hg
  have hp : graphSystem.prefixWord (2 + before) = [] := by
    rw [WordEventSystem.prefix_add, initial_diagonal_entry, scan.output, hp2, List.append_nil]
  have hphys : (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (2 + before)) = [] := by
    rw [graphRefinement.prefix_eq, hp]
  have hc : rankBase BlankFirst.zeros 0 1 8 = 0 := by simp [rankBase, bankAC]
  have hcount : rankBase BlankFirst.zeros 0 1 3 + 1 = 1 := by
    simp [rankBase, bankAC, bankRest, BlankFirst.zeros]
  obtain ⟨duration, pad, nextDuration, nextPad, finish, _, _, hgood, hstate, hconfig, hprefix, _⟩ :=
    selected_rank_third_field_zero_cleanup (2+before) 1 (rankBase BlankFirst.zeros 0 1)
      (BlankFirst.reserve ++ List.replicate padding 0) hc hcount hgraph
  refine ⟨graphRefinement.boundary ((2+before) + thirdCleanupDuration
    (rankBase BlankFirst.zeros 0 1) 1 (BlankFirst.reserve ++ List.replicate padding 0)
      duration pad nextDuration nextPad), finish, hgood, ?_, hconfig, ?_⟩
  · rw [hstate]; rfl
  · simpa [hphys, thirdFieldValue, rankBase, bankAC, bankRest, BlankFirst.zeros,
      Cantor.unpair, Cantor.unpairAux, PASoundness.UnaryCodec.unary] using hprefix

end PASoundness.M236.OccurrenceGraph
