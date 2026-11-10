import PASoundness.M236GraphRankCount
/-! An unpairing row schema shared by the selected scheduler occurrences. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

structure UnpairRows (k : Nat) : Prop where
  restDec : sourceRows[k]? = some ("3.k.rest.decnz", k+1, some (k+8))
  cInc : sourceRows[k+1]? = some ("3.k.c.inc", k+2, none)
  aDec : sourceRows[k+2]? = some ("3.k.a.decnz", k+3, some (k+4))
  jump3 : sourceRows[k+3]? = some ("jump", k+7, none)
  cDec : sourceRows[k+4]? = some ("3.k.c.decnz", k+5, some (k+7))
  aInc : sourceRows[k+5]? = some ("3.k.a.inc", k+6, none)
  jump6 : sourceRows[k+6]? = some ("jump", k+4, none)
  jump7 : sourceRows[k+7]? = some ("jump", k, none)
  drainDec : sourceRows[k+8]? = some ("3.k.c.decnz", k+9, some (k+11))
  restInc : sourceRows[k+9]? = some ("3.k.rest.inc", k+10, none)
  jump10 : sourceRows[k+10]? = some ("jump", k+8, none)

theorem generic_unpair_rows_7 : UnpairRows 7 := by constructor <;> decide
theorem generic_unpair_rows_30 : UnpairRows 30 := by constructor <;> decide
theorem generic_unpair_rows_57 : UnpairRows 57 := by constructor <;> decide
theorem generic_unpair_rows_84 : UnpairRows 84 := by constructor <;> decide

theorem generic_dec_rest (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (n a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC k base (n+1) a c reserve) =
      (cfgRAC (k+1) base n a c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.restDec, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, bankRest, RegisterMachine.write])

theorem generic_zero_rest (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC k base 0 a c reserve) = (cfgRAC (k+8) base 0 a c reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.restDec, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]


theorem generic_inc_c (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC (k+1) base rest a c reserve) =
      (cfgRAC (k+2) base rest a (c+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.cInc, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, bankRest, RegisterMachine.write])

theorem generic_dec_a (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (rest n c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC (k+2) base rest (n+1) c reserve) =
      (cfgRAC (k+3) base rest n c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.aDec, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, bankRest, RegisterMachine.write])

theorem generic_zero_a (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (rest c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC (k+2) base rest 0 c reserve) =
      (cfgRAC (k+4) base rest 0 c reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.aDec, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]

theorem generic_jump3 (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC (k+3) base rest a c reserve) =
      (cfgRAC (k+7) base rest a c reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.jump3, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]

theorem generic_dec_c (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (rest a n : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC (k+4) base rest a (n+1) reserve) =
      (cfgRAC (k+5) base rest a n (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.cDec, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, bankRest, RegisterMachine.write])

theorem generic_zero_c (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (rest a : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC (k+4) base rest a 0 reserve) =
      (cfgRAC (k+7) base rest a 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.cDec, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]

theorem generic_inc_a (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC (k+5) base rest a c reserve) =
      (cfgRAC (k+6) base rest (a+1) c reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.aInc, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, bankRest, RegisterMachine.write])

theorem generic_jump6 (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC (k+6) base rest a c reserve) =
      (cfgRAC (k+4) base rest a c reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.jump6, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]

theorem generic_jump7 (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC (k+7) base rest a c reserve) =
      (cfgRAC (k) base rest a c reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.jump7, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]

theorem generic_drain_dec (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (rest a n : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC (k+8) base rest a (n+1) reserve) =
      (cfgRAC (k+9) base rest a n (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.drainDec, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, bankRest, RegisterMachine.write])

theorem generic_drain_zero (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (rest a : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC (k+8) base rest a 0 reserve) =
      (cfgRAC (k+11) base rest a 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.drainDec, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]

theorem generic_inc_rest (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC (k+9) base rest a c reserve) =
      (cfgRAC (k+10) base (rest+1) a c reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.restInc, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, bankRest, RegisterMachine.write])

theorem generic_jump10 (k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC (k+10) base rest a c reserve) =
      (cfgRAC (k+8) base rest a c reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, rows.jump10, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]


theorem generic_move_cycle (k : Nat) (rows : UnpairRows k) (base : RegisterMachine.Bank 9)
    (rest a n : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgRAC (k+4) base rest a (n+1) reserve) 3
      (cfgRAC (k+4) base rest (a+1) n (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (generic_dec_c k rows base rest a n reserve)
  have h2 := WordEventSystem.Block.single graphSystem (generic_inc_a k rows base rest a n (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (generic_jump6 k rows base rest (a+1) n (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem generic_move_all (n k : Nat) (rows : UnpairRows k) (base : RegisterMachine.Bank 9)
    (rest a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgRAC (k+4) base rest a n reserve) (3*n)
      (cfgRAC (k+4) base rest (a+n) 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing a reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgRAC (k+4) base rest a 0 reserve)
  | succ n ih =>
    have h := (generic_move_cycle k rows base rest a n reserve).trans graphSystem (ih (a+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem generic_move_c_to_a (n k : Nat) (rows : UnpairRows k) (base : RegisterMachine.Bank 9)
    (rest a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgRAC (k+4) base rest a n reserve) (3*n+2)
      (cfgRAC k base rest (a+n) 0 (reserve ++ List.replicate n 0)) [] := by
  have h1 := generic_move_all n k rows base rest a reserve
  have h2 := WordEventSystem.Block.single graphSystem (generic_zero_c k rows base rest (a+n) (reserve ++ List.replicate n 0))
  have h3 := WordEventSystem.Block.single graphSystem (generic_jump7 k rows base rest (a+n) 0 (reserve ++ List.replicate n 0))
  simpa [Nat.add_assoc] using (h1.trans graphSystem h2).trans graphSystem h3

theorem generic_diagonal_positive (k : Nat) (rows : UnpairRows k) (base : RegisterMachine.Bank 9)
    (rest a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgRAC k base (rest+1) (a+1) c reserve) 5
      (cfgRAC k base rest a (c+1) ((reserve ++ [0]) ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (generic_dec_rest k rows base rest (a+1) c reserve)
  have h2 := WordEventSystem.Block.single graphSystem (generic_inc_c k rows base rest (a+1) c (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (generic_dec_a k rows base rest a (c+1) (reserve ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (generic_jump3 k rows base rest a (c+1) ((reserve ++ [0]) ++ [0]))
  have h5 := WordEventSystem.Block.single graphSystem (generic_jump7 k rows base rest a (c+1) ((reserve ++ [0]) ++ [0]))
  simpa using ((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5)

theorem generic_diagonal_zero (k : Nat) (rows : UnpairRows k) (base : RegisterMachine.Bank 9)
    (rest c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgRAC k base (rest+1) 0 c reserve) (3*(c+1)+5)
      (cfgRAC k base rest (c+1) 0 ((reserve ++ [0]) ++ List.replicate (c+1) 0)) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (generic_dec_rest k rows base rest 0 c reserve)
  have h2 := WordEventSystem.Block.single graphSystem (generic_inc_c k rows base rest 0 c (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (generic_zero_a k rows base rest (c+1) (reserve ++ [0]))
  have h4 := generic_move_c_to_a (c+1) k rows base rest 0 (reserve ++ [0])
  have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4
  have ht : 3 + (3*(c+1)+2) = 3*(c+1)+5 := by omega
  simpa only [Nat.zero_add, List.nil_append, Nat.reduceAdd, ht] using h

theorem generic_diagonal_phase (remaining k : Nat) (rows : UnpairRows k) (base : RegisterMachine.Bank 9)
    (a c : Nat) (reserve : List Nat) :
    ∃ duration padding, remaining+1 ≤ duration ∧
      graphSystem.Block (cfgRAC k base remaining a c reserve) duration
        (cfgRAC (k+8) base 0 (M236.UnpairDiagonal.walk remaining (a,c)).1
          (M236.UnpairDiagonal.walk remaining (a,c)).2
          (reserve ++ List.replicate padding 0)) [] := by
  induction remaining generalizing a c reserve with
  | zero =>
    refine ⟨1, 0, by omega, ?_⟩
    simpa [M236.UnpairDiagonal.walk] using WordEventSystem.Block.single graphSystem (generic_zero_rest k rows base a c reserve)
  | succ n ih =>
    cases a with
    | zero =>
      obtain ⟨duration, padding, ht, htail⟩ := ih (c+1) 0 ((reserve ++ [0]) ++ List.replicate (c+1) 0)
      have h := (generic_diagonal_zero k rows base n c reserve).trans graphSystem htail
      refine ⟨3*(c+1)+5+duration, (c+2)+padding, by omega, ?_⟩
      have hres : ((reserve ++ [0]) ++ List.replicate (c+1) 0) ++ List.replicate padding 0 =
          reserve ++ List.replicate ((c+2)+padding) 0 := by
        have hrep : List.replicate (c+2) (0 : Nat) = 0 :: List.replicate (c+1) 0 := rfl
        conv_rhs => rw [List.replicate_add, hrep]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [← hres]
      simpa only [M236.UnpairDiagonal.walk, M236.UnpairDiagonal.next,
        Prod.fst, Prod.snd, List.nil_append] using h
    | succ a =>
      obtain ⟨duration, padding, ht, htail⟩ := ih a (c+1) ((reserve ++ [0]) ++ [0])
      have h := (generic_diagonal_positive k rows base n a c reserve).trans graphSystem htail
      refine ⟨5+duration, 2+padding, by omega, ?_⟩
      have hres : ((reserve ++ [0]) ++ [0]) ++ List.replicate padding 0 =
          reserve ++ List.replicate (2+padding) 0 := by
        conv_rhs => rw [List.replicate_add]
        simp only [List.replicate_succ, List.replicate_zero, List.append_assoc, List.cons_append, List.nil_append]
      rw [← hres]
      simpa only [M236.UnpairDiagonal.walk, M236.UnpairDiagonal.next,
        Prod.fst, Prod.snd, List.nil_append] using h

/-- Starting with a=c=0, the graph's finite scan computes the exact Cantor
inverse of its arbitrary input. -/
theorem generic_diagonal_unpair (n k : Nat) (rows : UnpairRows k) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgRAC k base n 0 0 reserve) duration
        (cfgRAC (k+8) base 0 (Cantor.unpair n).1 (Cantor.unpair n).2
          (reserve ++ List.replicate padding 0)) [] := by
  simpa only [M236.UnpairDiagonal.walk_zero] using generic_diagonal_phase n k rows base 0 0 reserve



theorem generic_drain_cycle (k : Nat) (rows : UnpairRows k) (base : RegisterMachine.Bank 9)
    (rest a n : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgRAC (k+8) base rest a (n+1) reserve) 3
      (cfgRAC (k+8) base (rest+1) a n (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (generic_drain_dec k rows base rest a n reserve)
  have h2 := WordEventSystem.Block.single graphSystem (generic_inc_rest k rows base rest a n (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (generic_jump10 k rows base (rest+1) a n (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem generic_drain_all (n k : Nat) (rows : UnpairRows k) (base : RegisterMachine.Bank 9)
    (rest a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgRAC (k+8) base rest a n reserve) (3*n)
      (cfgRAC (k+8) base (rest+n) a 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing rest reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgRAC (k+8) base rest a 0 reserve)
  | succ n ih =>
    have h := (generic_drain_cycle k rows base rest a n reserve).trans graphSystem (ih (rest+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem generic_drain_finish (n k : Nat) (rows : UnpairRows k) (base : RegisterMachine.Bank 9)
    (rest a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgRAC (k+8) base rest a n reserve) (3*n+1)
      (cfgRAC (k+11) base (rest+n) a 0 (reserve ++ List.replicate n 0)) [] := by
  have h1 := generic_drain_all n k rows base rest a reserve
  have h2 := WordEventSystem.Block.single graphSystem
    (generic_drain_zero k rows base (rest+n) a (reserve ++ List.replicate n 0))
  simpa using h1.trans graphSystem h2

/-- Every checked occurrence of this row schema silently computes Cantor's
inverse on an arbitrary input, with positive finite progress and zero padding. -/
theorem generic_unpair (n k : Nat) (rows : UnpairRows k) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgRAC k base n 0 0 reserve) duration
        (cfgRAC (k+11) base (Cantor.unpair n).2 (Cantor.unpair n).1 0
          (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨duration, padding, ht, hscan⟩ := generic_diagonal_unpair n k rows base reserve
  have hfinish := generic_drain_finish (Cantor.unpair n).2 k rows base 0 (Cantor.unpair n).1
    (reserve ++ List.replicate padding 0)
  have h := hscan.trans graphSystem hfinish
  refine ⟨duration + (3*(Cantor.unpair n).2+1), padding+(Cantor.unpair n).2, by omega, ?_⟩
  have hres : (reserve ++ List.replicate padding 0) ++ List.replicate (Cantor.unpair n).2 0 =
      reserve ++ List.replicate (padding+(Cantor.unpair n).2) 0 := by
    conv_rhs => rw [List.replicate_add]
    simp only [List.append_assoc]
  rw [← hres]
  simpa only [Nat.zero_add, List.nil_append] using h


/-- Lift a checked schema occurrence at an explicitly reachable entry to
the actual selected blank-start execution. -/
theorem selected_generic_unpair (i n k : Nat) (rows : UnpairRows k)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (h : graphSystem.run i = cfgRAC k base n 0 0 reserve) :
    ∃ duration padding finish,
      n+1 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgRAC (k+11) base (Cantor.unpair n).2 (Cantor.unpair n).1 0
        (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i + duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i + duration) := by
  obtain ⟨duration, padding, ht, block⟩ := generic_unpair n k rows base reserve
  have hr : graphSystem.run (i+duration) =
      cfgRAC (k+11) base (Cantor.unpair n).2 (Cantor.unpair n).1 0
        (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hs, hc⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hs.trans hr, hc, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega


/-- The selected scheduler's unpairing block at occurrence 30. -/
theorem unpair_at_30 (n : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgRAC 30 base n 0 0 reserve) duration
        (cfgRAC 41 base (Cantor.unpair n).2 (Cantor.unpair n).1 0
          (reserve ++ List.replicate padding 0)) [] := by
  simpa using generic_unpair n 30 generic_unpair_rows_30 base reserve

/-- The selected scheduler's unpairing block at occurrence 57. -/
theorem unpair_at_57 (n : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgRAC 57 base n 0 0 reserve) duration
        (cfgRAC 68 base (Cantor.unpair n).2 (Cantor.unpair n).1 0
          (reserve ++ List.replicate padding 0)) [] := by
  simpa using generic_unpair n 57 generic_unpair_rows_57 base reserve

/-- The selected scheduler's unpairing block at occurrence 84. -/
theorem unpair_at_84 (n : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgRAC 84 base n 0 0 reserve) duration
        (cfgRAC 95 base (Cantor.unpair n).2 (Cantor.unpair n).1 0
          (reserve ++ List.replicate padding 0)) [] := by
  simpa using generic_unpair n 84 generic_unpair_rows_84 base reserve


/-- The rank-transfer exit is a second-unpair entry when its c register is zero. -/
theorem count_exit_to_second_unpair (base : RegisterMachine.Bank 9) (count : Nat)
    (reserve : List Nat) (hc : base 8 = 0) :
    cfgCountA 30 base count 0 reserve =
      cfgRAC 30 (bankCountA base count 0) (base 2) 0 0 reserve := by
  unfold cfgCountA cfgRAC cfgAC
  congr 1
  funext i
  fin_cases i <;> simp [bankCountA, bankAC, bankRest, hc]

/-- Emit a rank, transfer it to the counter, and unpair the remaining
address code; no assumption bounds either value. -/
theorem emit_count_then_second_unpair (n : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) :
    ∃ duration padding, base 2 + 1 ≤ duration ∧
      graphSystem.Block (cfgAS 19 base n 0 reserve) (((7*n+3) + (3*n+1)) + duration)
        (cfgRAC 41 (bankCountA (bankAS base n 0) (base 3+n) 0)
          (Cantor.unpair (base 2)).2 (Cantor.unpair (base 2)).1 0
          ((((reserve ++ List.replicate n 0) ++ List.replicate n 0) ++ List.replicate n 0) ++
            List.replicate padding 0))
        (PASoundness.UnaryCodec.unary n) := by
  have hem := emit_then_rank_to_count n base reserve
  have hc' : bankAS base n 0 8 = 0 := by simp [bankAS, hc]
  have hr : bankAS base n 0 2 = base 2 := by simp [bankAS]
  rw [count_exit_to_second_unpair (bankAS base n 0) (base 3+n) _ hc', hr] at hem
  obtain ⟨duration, padding, ht, hu⟩ := unpair_at_30 (base 2)
    (bankCountA (bankAS base n 0) (base 3+n) 0)
    (((reserve ++ List.replicate n 0) ++ List.replicate n 0) ++ List.replicate n 0)
  refine ⟨duration, padding, ht, ?_⟩
  simpa only [List.append_nil] using hem.trans graphSystem hu


/-- Physical lift of the composed field and second unpairing at a reachable
entry of the one blank-start execution. -/
theorem selected_emit_count_second_unpair (i n : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0)
    (h : graphSystem.run i = cfgAS 19 base n 0 reserve) :
    ∃ duration padding finish, base 2 + 1 ≤ duration ∧ Good finish ∧
      finish.graphState =
        cfgRAC 41 (bankCountA (bankAS base n 0) (base 3+n) 0)
          (Cantor.unpair (base 2)).2 (Cantor.unpair (base 2)).1 0
          ((((reserve ++ List.replicate n 0) ++ List.replicate n 0) ++ List.replicate n 0) ++
            List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + (((7*n+3) + (3*n+1)) + duration))) ∧
      (machineWordSystem machine machineLabels).prefixWord
          (graphRefinement.boundary (i + (((7*n+3) + (3*n+1)) + duration))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.unary n ∧
      graphRefinement.boundary i <
        graphRefinement.boundary (i + (((7*n+3) + (3*n+1)) + duration)) := by
  obtain ⟨duration, padding, ht, block⟩ := emit_count_then_second_unpair n base reserve hc
  have hr : graphSystem.run (i + (((7*n+3) + (3*n+1)) + duration)) =
      cfgRAC 41 (bankCountA (bankAS base n 0) (base 3+n) 0)
        (Cantor.unpair (base 2)).2 (Cantor.unpair (base 2)).1 0
        ((((reserve ++ List.replicate n 0) ++ List.replicate n 0) ++ List.replicate n 0) ++
          List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i + (((7*n+3) + (3*n+1)) + duration)) =
      graphSystem.prefixWord i ++ PASoundness.UnaryCodec.unary n := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hc'⟩ := graphRefinement.related
    (i + (((7*n+3) + (3*n+1)) + duration))
  refine ⟨duration, padding, finish, ht, hg, hs.trans hr, hc', ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega


/-- From blank tape, the selected run emits its first rank field and reaches
the exit of the second, zero-input unpairing. -/
theorem initial_second_unpair_on_selected :
    ∃ before duration finish,
      Good finish ∧ finish.graphState.index = 41 ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary ((2 + before) + (14 + duration))) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary ((2 + before) + (14 + duration))) = [true, false] := by
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
  have hc : rankBase BlankFirst.zeros 0 1 8 = 0 := by simp [rankBase, bankAC]
  obtain ⟨duration, padding', finish, hd, hgood, hstate, hconfig, hprefix, hpositive⟩ :=
    selected_emit_count_second_unpair (2+before) 1 (rankBase BlankFirst.zeros 0 1)
      (BlankFirst.reserve ++ List.replicate padding 0) hc hgraph
  have hphys : (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (2 + before)) = [] := by
    rw [graphRefinement.prefix_eq, hp]
  refine ⟨before, duration, finish, hgood, ?_, ?_, ?_⟩
  · rw [hstate]; rfl
  · simpa using hconfig
  · simpa [PASoundness.UnaryCodec.unary, hphys] using hprefix

end PASoundness.M236.OccurrenceGraph
