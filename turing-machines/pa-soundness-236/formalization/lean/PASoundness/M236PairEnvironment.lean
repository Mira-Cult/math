import PASoundness.M236CoordinateBudget

/-! Prepared environment-consing routines in three signed-evaluator branches. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

structure PairEnvRows (k : Nat) : Prop where
  row0 : sourceRows[k]? = some ("3.k.env.decnz", k+1, some (k+4))
  row1 : sourceRows[k+1]? = some ("3.k.a.inc", k+2, none)
  row2 : sourceRows[k+2]? = some ("3.k.c.inc", k+3, none)
  row3 : sourceRows[k+3]? = some ("jump", k, none)
  row4 : sourceRows[k+4]? = some ("3.k.a.decnz", k+5, some (k+10))
  row5 : sourceRows[k+5]? = some ("3.k.c.inc", k+6, none)
  row6 : sourceRows[k+6]? = some ("3.k.a.decnz", k+7, some (k+9))
  row7 : sourceRows[k+7]? = some ("3.k.env.inc", k+8, none)
  row8 : sourceRows[k+8]? = some ("jump", k+6, none)
  row9 : sourceRows[k+9]? = some ("jump", k, none)
  row10 : sourceRows[k+10]? = some ("3.k.c.decnz", k+11, some (k+13))
  row11 : sourceRows[k+11]? = some ("3.k.env.inc", k+12, none)
  row12 : sourceRows[k+12]? = some ("jump", k+10, none)

theorem pair_env_rows_148 : PairEnvRows 148 := by constructor <;> decide
theorem pair_env_rows_237 : PairEnvRows 237 := by constructor <;> decide
theorem pair_env_rows_414 : PairEnvRows 414 := by constructor <;> decide
theorem pair_env_rows_594 : PairEnvRows 594 := by constructor <;> decide

theorem pair_env_dec148 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget k base count (env+1) a c reserve) =
      (cfgBudget (k+1) base count env a c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row0, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem pair_env_zero148 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget k base count 0 a c reserve) = (cfgBudget (k+4) base count 0 a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row0, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]

theorem pair_env_inc149 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+1) base count env a c reserve) = (cfgBudget (k+2) base count env (a+1) c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row1, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem pair_env_inc150 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+2) base count env a c reserve) = (cfgBudget (k+3) base count env a (c+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row2, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem pair_env_jump151 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+3) base count env a c reserve) = (cfgBudget k base count env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row3, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem pair_env_dec152 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+4) base count env (a+1) c reserve) =
      (cfgBudget (k+5) base count env a c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row4, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem pair_env_zero152 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+4) base count env 0 c reserve) = (cfgBudget (k+10) base count env 0 c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row4, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]

theorem pair_env_inc153 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+5) base count env a c reserve) = (cfgBudget (k+6) base count env a (c+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row5, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem pair_env_dec154 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+6) base count env (a+1) c reserve) =
      (cfgBudget (k+7) base count env a c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row6, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem pair_env_zero154 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+6) base count env 0 c reserve) = (cfgBudget (k+9) base count env 0 c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row6, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]

theorem pair_env_inc155 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+7) base count env a c reserve) = (cfgBudget (k+8) base count (env+1) a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row7, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem pair_env_jump156 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+8) base count env a c reserve) = (cfgBudget (k+6) base count env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row8, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem pair_env_jump157 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+9) base count env a c reserve) = (cfgBudget k base count env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row9, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem pair_env_dec158 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+10) base count env a (c+1) reserve) =
      (cfgBudget (k+11) base count env a c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row10, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem pair_env_zero158 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+10) base count env a 0 reserve) = (cfgBudget (k+13) base count env a 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row10, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]

theorem pair_env_inc159 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+11) base count env a c reserve) = (cfgBudget (k+12) base count (env+1) a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row11, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem pair_env_jump160 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget (k+12) base count env a c reserve) = (cfgBudget (k+10) base count env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, rows.row12, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem pair_env_cycle148 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget k base count (env+1) a c reserve) 4
      (cfgBudget k base count env (a+1) (c+1) (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (pair_env_dec148 k rows base count env a c reserve)
  have h2 := WordEventSystem.Block.single graphSystem (pair_env_inc149 k rows base count env a c (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (pair_env_inc150 k rows base count env (a+1) c (reserve ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (pair_env_jump151 k rows base count env (a+1) (c+1) (reserve ++ [0]))
  simpa using ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4

theorem pair_env_many148 (k : Nat) (rows : PairEnvRows k) (n : Nat) (base : RegisterMachine.Bank 9) (count a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget k base count n a c reserve) (4*n)
      (cfgBudget k base count 0 (a+n) (c+n) (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing a c reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgBudget k base count 0 a c reserve)
  | succ n ih =>
    have h := (pair_env_cycle148 k rows base count n a c reserve).trans graphSystem (ih (a+1) (c+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem pair_env_transfer148 (k : Nat) (rows : PairEnvRows k) (n : Nat) (base : RegisterMachine.Bank 9) (count a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget k base count n a c reserve) (4*n+1)
      (cfgBudget (k+4) base count 0 (a+n) (c+n) (reserve ++ List.replicate n 0)) [] := by
  have h := (pair_env_many148 k rows n base count a c reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (pair_env_zero148 k rows base count (a+n) (c+n) (reserve ++ List.replicate n 0)))
  simpa using h

theorem pair_env_cycle154 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget (k+6) base count env (a+1) c reserve) 3
      (cfgBudget (k+6) base count (env+1) a c (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (pair_env_dec154 k rows base count env a c reserve)
  have h2 := WordEventSystem.Block.single graphSystem (pair_env_inc155 k rows base count env a c (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (pair_env_jump156 k rows base count (env+1) a c (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem pair_env_many154 (k : Nat) (rows : PairEnvRows k) (n : Nat) (base : RegisterMachine.Bank 9) (count env c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget (k+6) base count env n c reserve) (3*n)
      (cfgBudget (k+6) base count (env+n) 0 c (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing env reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgBudget (k+6) base count env 0 c reserve)
  | succ n ih =>
    have h := (pair_env_cycle154 k rows base count env n c reserve).trans graphSystem (ih (env+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem pair_env_transfer154 (k : Nat) (rows : PairEnvRows k) (n : Nat) (base : RegisterMachine.Bank 9) (count env c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget (k+6) base count env n c reserve) (3*n+2)
      (cfgBudget k base count (env+n) 0 c (reserve ++ List.replicate n 0)) [] := by
  have h1 := pair_env_many154 k rows n base count env c reserve
  have h2 := WordEventSystem.Block.single graphSystem (pair_env_zero154 k rows base count (env+n) c (reserve ++ List.replicate n 0))
  have h3 := WordEventSystem.Block.single graphSystem (pair_env_jump157 k rows base count (env+n) 0 c (reserve ++ List.replicate n 0))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem pair_env_cycle158 (k : Nat) (rows : PairEnvRows k) (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget (k+10) base count env a (c+1) reserve) 3
      (cfgBudget (k+10) base count (env+1) a c (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (pair_env_dec158 k rows base count env a c reserve)
  have h2 := WordEventSystem.Block.single graphSystem (pair_env_inc159 k rows base count env a c (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (pair_env_jump160 k rows base count (env+1) a c (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem pair_env_many158 (k : Nat) (rows : PairEnvRows k) (n : Nat) (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget (k+10) base count env a n reserve) (3*n)
      (cfgBudget (k+10) base count (env+n) a 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing env reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgBudget (k+10) base count env a 0 reserve)
  | succ n ih =>
    have h := (pair_env_cycle158 k rows base count env a n reserve).trans graphSystem (ih (env+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem pair_env_transfer158 (k : Nat) (rows : PairEnvRows k) (n : Nat) (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget (k+10) base count env a n reserve) (3*n+1)
      (cfgBudget (k+13) base count (env+n) a 0 (reserve ++ List.replicate n 0)) [] := by
  have h := (pair_env_many158 k rows n base count env a reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (pair_env_zero158 k rows base count (env+n) a (reserve ++ List.replicate n 0)))
  simpa using h

/-- The triangular loop consumes `a`, leaves the triangular increment in `c`,
and has finite positive duration and an explicitly finite all-zero reserve. -/
theorem pair_env_triangle (k : Nat) (rows : PairEnvRows k) (n : Nat) (base : RegisterMachine.Bank 9) (count c : Nat) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgBudget (k+4) base count 0 n c reserve) duration
        (cfgBudget (k+10) base count 0 0 (c + Cantor.triangle n)
          (reserve ++ List.replicate padding 0)) [] := by
  induction n generalizing c reserve with
  | zero =>
    refine ⟨1, 0, by omega, ?_⟩
    simpa [Cantor.triangle] using WordEventSystem.Block.single graphSystem
      (pair_env_zero152 k rows base count 0 c reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (pair_env_dec152 k rows base count 0 n c reserve)
    have h2 := WordEventSystem.Block.single graphSystem (pair_env_inc153 k rows base count 0 n c (reserve ++ [0]))
    have h3 := pair_env_transfer154 k rows n base count 0 (c+1) (reserve ++ [0])
    have h4 := pair_env_transfer148 k rows n base count 0 (c+1) ((reserve ++ [0]) ++ List.replicate n 0)
    simp only [Nat.zero_add] at h3 h4
    obtain ⟨duration, padding, ht, h5⟩ := ih (c+1+n)
      (((reserve ++ [0]) ++ List.replicate n 0) ++ List.replicate n 0)
    have h := ((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5)
    refine ⟨1+1+(3*n+2)+(4*n+1)+duration, 1+n+n+padding, by omega, ?_⟩
    have hc : c+1+n+Cantor.triangle n = c+Cantor.triangle (n+1) := by
      simp only [Cantor.triangle]
      omega
    have hr : (((reserve ++ [0]) ++ List.replicate n 0) ++ List.replicate n 0) ++
        List.replicate padding 0 = reserve ++ List.replicate (1+n+n+padding) 0 := by
      simp only [List.replicate_add, List.replicate_succ, List.replicate_zero,
        List.append_assoc]
    simp only [List.nil_append] at h
    rw [hc, hr] at h
    exact h


/-- The prepared environment-consing block computes `c + pair a env` in
the `env` register, consumes `a` and `c`, and preserves every other register.
The original scratch value is part of `base` and is unchanged. Output is
empty and reserve growth consists of finitely many zero blocks. -/
theorem pair_environment_accumulating (k : Nat) (rows : PairEnvRows k)
    (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgBudget k base count env a c reserve) duration
        (cfgBudget (k+13) base count (c + Cantor.pair a env) 0 0
          (reserve ++ List.replicate padding 0)) [] := by
  have h1 := pair_env_transfer148 k rows env base count a c reserve
  obtain ⟨duration, padding, ht, h2⟩ := pair_env_triangle k rows (a+env) base count (c+env)
    (reserve ++ List.replicate env 0)
  have h3 := pair_env_transfer158 k rows (c+env+Cantor.triangle (a+env)) base count 0 0
    ((reserve ++ List.replicate env 0) ++ List.replicate padding 0)
  simp only [Nat.zero_add] at h3
  have h := (h1.trans graphSystem h2).trans graphSystem h3
  refine ⟨4*env+1+duration+(3*(c+env+Cantor.triangle (a+env))+1),
    env+padding+(c+env+Cantor.triangle (a+env)), by omega, ?_⟩
  have hval : c+env+Cantor.triangle (a+env) = c+Cantor.pair a env := by
    simp only [Cantor.pair]
    omega
  have hr : ((reserve ++ List.replicate env 0) ++ List.replicate padding 0) ++
      List.replicate (c+env+Cantor.triangle (a+env)) 0 =
        reserve ++ List.replicate (env+padding+(c+env+Cantor.triangle (a+env))) 0 := by
    simp only [List.replicate_add, List.append_assoc]
  simp only [List.nil_append] at h
  rw [hr, hval] at h
  rw [hval]
  exact h

/-- Clean accumulator gives the exact environment encoding, including the
producer's orientation `pair newValue oldEnvironment`. -/
theorem pair_environment (k : Nat) (rows : PairEnvRows k)
    (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgBudget k base count env a 0 reserve) duration
        (cfgBudget (k+13) base count (Cantor.pair a env) 0 0
          (reserve ++ List.replicate padding 0)) [] := by
  simpa only [Nat.zero_add] using pair_environment_accumulating k rows base count env a 0 reserve

theorem pair_environment_237 (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgBudget 237 base count env a 0 reserve) duration
        (cfgBudget 250 base count (Cantor.pair a env) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  simpa using pair_environment 237 pair_env_rows_237 base count env a reserve

theorem pair_environment_414 (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgBudget 414 base count env a 0 reserve) duration
        (cfgBudget 427 base count (Cantor.pair a env) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  simpa using pair_environment 414 pair_env_rows_414 base count env a reserve

theorem pair_environment_594 (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgBudget 594 base count env a 0 reserve) duration
        (cfgBudget 607 base count (Cantor.pair a env) 0 0 (reserve ++ List.replicate padding 0)) [] := by
  simpa using pair_environment 594 pair_env_rows_594 base count env a reserve

/-- Physical lifting requires actual reachability of the prepared graph entry. -/
theorem selected_pair_environment (k i : Nat) (rows : PairEnvRows k)
    (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat)
    (h : graphSystem.run i = cfgBudget k base count env a 0 reserve) :
    ∃ duration padding finish, 0 < duration ∧ Good finish ∧
      finish.graphState = cfgBudget (k+13) base count (Cantor.pair a env) 0 0
        (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgBudget (k+13) base count (Cantor.pair a env) 0 0
        (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := pair_environment k rows base count env a reserve
  have hr : graphSystem.run (i+duration) = cfgBudget (k+13) base count (Cantor.pair a env) 0 0
      (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
