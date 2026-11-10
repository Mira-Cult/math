import PASoundness.M236CoordinateBudget

/-! Prepared silent graph computation of the initial encoded environment. -/
set_option maxRecDepth 655655
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

theorem init_env_row145 : sourceRows[145]? = some ("3.k.env.decnz", 146, some 148) := by decide
theorem init_env_row146 : sourceRows[146]? = some ("3.k.a.inc", 147, none) := by decide
theorem init_env_row147 : sourceRows[147]? = some ("jump", 145, none) := by decide
theorem init_env_row148 : sourceRows[148]? = some ("3.k.env.decnz", 149, some 152) := by decide
theorem init_env_row149 : sourceRows[149]? = some ("3.k.a.inc", 150, none) := by decide
theorem init_env_row150 : sourceRows[150]? = some ("3.k.c.inc", 151, none) := by decide
theorem init_env_row151 : sourceRows[151]? = some ("jump", 148, none) := by decide
theorem init_env_row152 : sourceRows[152]? = some ("3.k.a.decnz", 153, some 158) := by decide
theorem init_env_row153 : sourceRows[153]? = some ("3.k.c.inc", 154, none) := by decide
theorem init_env_row154 : sourceRows[154]? = some ("3.k.a.decnz", 155, some 157) := by decide
theorem init_env_row155 : sourceRows[155]? = some ("3.k.env.inc", 156, none) := by decide
theorem init_env_row156 : sourceRows[156]? = some ("jump", 154, none) := by decide
theorem init_env_row157 : sourceRows[157]? = some ("jump", 148, none) := by decide
theorem init_env_row158 : sourceRows[158]? = some ("3.k.c.decnz", 159, some 161) := by decide
theorem init_env_row159 : sourceRows[159]? = some ("3.k.env.inc", 160, none) := by decide
theorem init_env_row160 : sourceRows[160]? = some ("jump", 158, none) := by decide

theorem init_env_dec145 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 145 base count (env+1) a c reserve) =
      (cfgBudget 146 base count env a c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row145, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem init_env_zero145 (base : RegisterMachine.Bank 9) (count a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 145 base count 0 a c reserve) = (cfgBudget 148 base count 0 a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row145, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]

theorem init_env_inc146 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 146 base count env a c reserve) = (cfgBudget 147 base count env (a+1) c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row146, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem init_env_jump147 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 147 base count env a c reserve) = (cfgBudget 145 base count env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row147, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem init_env_dec148 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 148 base count (env+1) a c reserve) =
      (cfgBudget 149 base count env a c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row148, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem init_env_zero148 (base : RegisterMachine.Bank 9) (count a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 148 base count 0 a c reserve) = (cfgBudget 152 base count 0 a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row148, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]

theorem init_env_inc149 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 149 base count env a c reserve) = (cfgBudget 150 base count env (a+1) c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row149, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem init_env_inc150 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 150 base count env a c reserve) = (cfgBudget 151 base count env a (c+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row150, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem init_env_jump151 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 151 base count env a c reserve) = (cfgBudget 148 base count env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row151, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem init_env_dec152 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 152 base count env (a+1) c reserve) =
      (cfgBudget 153 base count env a c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row152, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem init_env_zero152 (base : RegisterMachine.Bank 9) (count env c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 152 base count env 0 c reserve) = (cfgBudget 158 base count env 0 c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row152, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]

theorem init_env_inc153 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 153 base count env a c reserve) = (cfgBudget 154 base count env a (c+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row153, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem init_env_dec154 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 154 base count env (a+1) c reserve) =
      (cfgBudget 155 base count env a c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row154, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem init_env_zero154 (base : RegisterMachine.Bank 9) (count env c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 154 base count env 0 c reserve) = (cfgBudget 157 base count env 0 c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row154, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]

theorem init_env_inc155 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 155 base count env a c reserve) = (cfgBudget 156 base count (env+1) a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row155, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem init_env_jump156 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 156 base count env a c reserve) = (cfgBudget 154 base count env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row156, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem init_env_jump157 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 157 base count env a c reserve) = (cfgBudget 148 base count env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row157, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem init_env_dec158 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 158 base count env a (c+1) reserve) =
      (cfgBudget 159 base count env a c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row158, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem init_env_zero158 (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 158 base count env a 0 reserve) = (cfgBudget 161 base count env a 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row158, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]

theorem init_env_inc159 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 159 base count env a c reserve) = (cfgBudget 160 base count (env+1) a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row159, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankBudget, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankBudget, RegisterMachine.write])

theorem init_env_jump160 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgBudget 160 base count env a c reserve) = (cfgBudget 158 base count env a c reserve, []) := by
  simp [graphSystem, graphNext, cfgBudget, init_env_row160, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem init_env_cycle145 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 145 base count (env+1) a c reserve) 3
      (cfgBudget 145 base count env (a+1) c (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (init_env_dec145 base count env a c reserve)
  have h2 := WordEventSystem.Block.single graphSystem (init_env_inc146 base count env a c (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (init_env_jump147 base count env (a+1) c (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem init_env_many145 (n : Nat) (base : RegisterMachine.Bank 9) (count a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 145 base count n a c reserve) (3*n)
      (cfgBudget 145 base count 0 (a+n) c (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing a reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgBudget 145 base count 0 a c reserve)
  | succ n ih =>
    have h := (init_env_cycle145 base count n a c reserve).trans graphSystem (ih (a+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem init_env_transfer145 (n : Nat) (base : RegisterMachine.Bank 9) (count a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 145 base count n a c reserve) (3*n+1)
      (cfgBudget 148 base count 0 (a+n) c (reserve ++ List.replicate n 0)) [] := by
  have h := (init_env_many145 n base count a c reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (init_env_zero145 base count (a+n) c (reserve ++ List.replicate n 0)))
  simpa using h

theorem init_env_cycle148 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 148 base count (env+1) a c reserve) 4
      (cfgBudget 148 base count env (a+1) (c+1) (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (init_env_dec148 base count env a c reserve)
  have h2 := WordEventSystem.Block.single graphSystem (init_env_inc149 base count env a c (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (init_env_inc150 base count env (a+1) c (reserve ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (init_env_jump151 base count env (a+1) (c+1) (reserve ++ [0]))
  simpa using ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4

theorem init_env_many148 (n : Nat) (base : RegisterMachine.Bank 9) (count a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 148 base count n a c reserve) (4*n)
      (cfgBudget 148 base count 0 (a+n) (c+n) (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing a c reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgBudget 148 base count 0 a c reserve)
  | succ n ih =>
    have h := (init_env_cycle148 base count n a c reserve).trans graphSystem (ih (a+1) (c+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem init_env_transfer148 (n : Nat) (base : RegisterMachine.Bank 9) (count a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 148 base count n a c reserve) (4*n+1)
      (cfgBudget 152 base count 0 (a+n) (c+n) (reserve ++ List.replicate n 0)) [] := by
  have h := (init_env_many148 n base count a c reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (init_env_zero148 base count (a+n) (c+n) (reserve ++ List.replicate n 0)))
  simpa using h

theorem init_env_cycle154 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 154 base count env (a+1) c reserve) 3
      (cfgBudget 154 base count (env+1) a c (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (init_env_dec154 base count env a c reserve)
  have h2 := WordEventSystem.Block.single graphSystem (init_env_inc155 base count env a c (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (init_env_jump156 base count (env+1) a c (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem init_env_many154 (n : Nat) (base : RegisterMachine.Bank 9) (count env c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 154 base count env n c reserve) (3*n)
      (cfgBudget 154 base count (env+n) 0 c (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing env reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgBudget 154 base count env 0 c reserve)
  | succ n ih =>
    have h := (init_env_cycle154 base count env n c reserve).trans graphSystem (ih (env+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem init_env_transfer154 (n : Nat) (base : RegisterMachine.Bank 9) (count env c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 154 base count env n c reserve) (3*n+2)
      (cfgBudget 148 base count (env+n) 0 c (reserve ++ List.replicate n 0)) [] := by
  have h1 := init_env_many154 n base count env c reserve
  have h2 := WordEventSystem.Block.single graphSystem (init_env_zero154 base count (env+n) c (reserve ++ List.replicate n 0))
  have h3 := WordEventSystem.Block.single graphSystem (init_env_jump157 base count (env+n) 0 c (reserve ++ List.replicate n 0))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem init_env_cycle158 (base : RegisterMachine.Bank 9) (count env a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 158 base count env a (c+1) reserve) 3
      (cfgBudget 158 base count (env+1) a c (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (init_env_dec158 base count env a c reserve)
  have h2 := WordEventSystem.Block.single graphSystem (init_env_inc159 base count env a c (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (init_env_jump160 base count (env+1) a c (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem init_env_many158 (n : Nat) (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 158 base count env a n reserve) (3*n)
      (cfgBudget 158 base count (env+n) a 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing env reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgBudget 158 base count env a 0 reserve)
  | succ n ih =>
    have h := (init_env_cycle158 base count env a n reserve).trans graphSystem (ih (env+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem init_env_transfer158 (n : Nat) (base : RegisterMachine.Bank 9) (count env a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgBudget 158 base count env a n reserve) (3*n+1)
      (cfgBudget 161 base count (env+n) a 0 (reserve ++ List.replicate n 0)) [] := by
  have h := (init_env_many158 n base count env a reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (init_env_zero158 base count (env+n) a (reserve ++ List.replicate n 0)))
  simpa using h

/-- The triangular loop consumes `a`, leaves the triangular increment in `c`,
and has finite positive duration and an explicitly finite all-zero reserve. -/
theorem init_env_triangle (n : Nat) (base : RegisterMachine.Bank 9) (count c : Nat) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgBudget 152 base count 0 n c reserve) duration
        (cfgBudget 158 base count 0 0 (c + Cantor.triangle n)
          (reserve ++ List.replicate padding 0)) [] := by
  induction n generalizing c reserve with
  | zero =>
    refine ⟨1, 0, by omega, ?_⟩
    simpa [Cantor.triangle] using WordEventSystem.Block.single graphSystem
      (init_env_zero152 base count 0 c reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (init_env_dec152 base count 0 n c reserve)
    have h2 := WordEventSystem.Block.single graphSystem (init_env_inc153 base count 0 n c (reserve ++ [0]))
    have h3 := init_env_transfer154 n base count 0 (c+1) (reserve ++ [0])
    have h4 := init_env_transfer148 n base count 0 (c+1) ((reserve ++ [0]) ++ List.replicate n 0)
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

/-- A clean prepared entry initializes the numeric environment to
`Cantor.pair y 0`, preserves all other bank registers and appends only finitely
many zero reserve blocks. This is a local graph block, not a reachability or
source-refinement assertion. -/
theorem initialize_environment (y : Nat) (base : RegisterMachine.Bank 9)
    (count : Nat) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgBudget 145 base count y 0 0 reserve) duration
        (cfgBudget 161 base count (Cantor.pair y 0) 0 0
          (reserve ++ List.replicate padding 0)) [] := by
  have h1 := init_env_transfer145 y base count 0 0 reserve
  simp only [Nat.zero_add] at h1
  have h2 := WordEventSystem.Block.single graphSystem
    (init_env_zero148 base count y 0 (reserve ++ List.replicate y 0))
  obtain ⟨duration, padding, ht, h3⟩ := init_env_triangle y base count 0 (reserve ++ List.replicate y 0)
  simp only [Nat.zero_add] at h3
  have h4 := init_env_transfer158 (Cantor.triangle y) base count 0 0
    ((reserve ++ List.replicate y 0) ++ List.replicate padding 0)
  simp only [Nat.zero_add] at h4
  have h := (((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4)
  refine ⟨3*y+1+1+duration+(3*Cantor.triangle y+1), y+padding+Cantor.triangle y, by omega, ?_⟩
  have hr : ((reserve ++ List.replicate y 0) ++ List.replicate padding 0) ++
      List.replicate (Cantor.triangle y) 0 =
        reserve ++ List.replicate (y+padding+Cantor.triangle y) 0 := by
    simp only [List.replicate_add, List.append_assoc]
  simp only [List.nil_append] at h
  rw [hr] at h
  simpa only [Cantor.pair, Nat.add_zero] using h

/-- Conditional physical lift: the selected execution must reach the displayed
prepared graph entry. -/
theorem selected_initialize_environment (i y : Nat) (base : RegisterMachine.Bank 9)
    (count : Nat) (reserve : List Nat)
    (h : graphSystem.run i = cfgBudget 145 base count y 0 0 reserve) :
    ∃ duration padding finish, 0 < duration ∧ Good finish ∧
      finish.graphState = cfgBudget 161 base count (Cantor.pair y 0) 0 0
        (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgBudget 161 base count (Cantor.pair y 0) 0 0
        (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := initialize_environment y base count reserve
  have hr : graphSystem.run (i+duration) = cfgBudget 161 base count (Cantor.pair y 0) 0 0
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
