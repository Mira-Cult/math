import PASoundness.M236EnvironmentLookup

/-! Prepared first operand lookup for the strict ordered atomic evaluator. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def cfgEnv (i : Nat) (base : RegisterMachine.Bank 9) (env a b c scratch : Nat)
    (reserve : List Nat) : GraphState :=
  cfgHalf i (RegisterMachine.write base 5 env) a b c scratch reserve

/-- The graph moves the encoded environment into b, traverses it, and stores
the selected value in env while retaining the suffix in scratch. -/
structure AtomFirstLookupRows (k : Nat) : Prop where
  decEnv : sourceRows[k]? = some ("3.k.env.decnz", k+1, some (k+3))
  incB : sourceRows[k+1]? = some ("3.k.b.inc", k+2, none)
  envJump : sourceRows[k+2]? = some ("jump", k, none)
  scan : EnvironmentLookupRows (k+3)
  decC : sourceRows[k+26]? = some ("3.k.c.decnz", k+27, some (k+29))
  incEnv : sourceRows[k+27]? = some ("3.k.env.inc", k+28, none)
  cJump : sourceRows[k+28]? = some ("jump", k+26, none)

theorem atom_first_lookup_rows_270 : AtomFirstLookupRows 270 := by constructor <;> first | constructor <;> constructor <;> decide
theorem atom_first_lookup_rows_447 : AtomFirstLookupRows 447 := by constructor <;> first | constructor <;> constructor <;> decide
theorem atom_first_lookup_rows_627 : AtomFirstLookupRows 627 := by constructor <;> first | constructor <;> constructor <;> decide

theorem atom_first_dec_env (k : Nat) (rows : AtomFirstLookupRows k) (base : RegisterMachine.Bank 9)
    (env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgEnv k base (env+1) a b c s reserve) =
      (cfgEnv (k+1) base env a b c s (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgEnv, cfgHalf, rows.decEnv, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom_first_zero_env (k : Nat) (rows : AtomFirstLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgEnv k base 0 a b c s reserve) = (cfgEnv (k+3) base 0 a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgEnv, cfgHalf, rows.decEnv, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem atom_first_inc_b (k : Nat) (rows : AtomFirstLookupRows k) (base : RegisterMachine.Bank 9)
    (env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgEnv (k+1) base env a b c s reserve) = (cfgEnv (k+2) base env a (b+1) c s reserve, []) := by
  simp [graphSystem, graphNext, cfgEnv, cfgHalf, rows.incB, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom_first_jump_env (k : Nat) (rows : AtomFirstLookupRows k) (base : RegisterMachine.Bank 9)
    (env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgEnv (k+2) base env a b c s reserve) = (cfgEnv k base env a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgEnv, cfgHalf, rows.envJump, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem atom_first_dec_c (k : Nat) (rows : AtomFirstLookupRows k) (base : RegisterMachine.Bank 9)
    (env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgEnv (k+26) base env a b (c+1) s reserve) =
      (cfgEnv (k+27) base env a b c s (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgEnv, cfgHalf, rows.decC, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom_first_zero_c (k : Nat) (rows : AtomFirstLookupRows k) (base : RegisterMachine.Bank 9)
    (env a b s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgEnv (k+26) base env a b 0 s reserve) = (cfgEnv (k+29) base env a b 0 s reserve, []) := by
  simp [graphSystem, graphNext, cfgEnv, cfgHalf, rows.decC, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem atom_first_inc_env (k : Nat) (rows : AtomFirstLookupRows k) (base : RegisterMachine.Bank 9)
    (env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgEnv (k+27) base env a b c s reserve) = (cfgEnv (k+28) base (env+1) a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgEnv, cfgHalf, rows.incEnv, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom_first_jump_c (k : Nat) (rows : AtomFirstLookupRows k) (base : RegisterMachine.Bank 9)
    (env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgEnv (k+28) base env a b c s reserve) = (cfgEnv (k+26) base env a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgEnv, cfgHalf, rows.cJump, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem atom_first_env_cycle (k : Nat) (rows : AtomFirstLookupRows k) (base : RegisterMachine.Bank 9)
    (env a b c s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgEnv k base (env+1) a b c s reserve) 3
      (cfgEnv k base env a (b+1) c s (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (atom_first_dec_env k rows base env a b c s reserve)
  have h2 := WordEventSystem.Block.single graphSystem (atom_first_inc_b k rows base env a b c s (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (atom_first_jump_env k rows base env a (b+1) c s (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem atom_first_env_many (n k : Nat) (rows : AtomFirstLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgEnv k base n a b c s reserve) (3*n)
      (cfgEnv k base 0 a (b+n) c s (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing b reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgEnv k base 0 a b c s reserve)
  | succ n ih =>
    have h := (atom_first_env_cycle k rows base n a b c s reserve).trans graphSystem (ih (b+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem atom_first_env_move (n k : Nat) (rows : AtomFirstLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgEnv k base n a b c s reserve) (3*n+1)
      (cfgEnv (k+3) base 0 a (b+n) c s (reserve ++ List.replicate n 0)) [] := by
  have h := (atom_first_env_many n k rows base a b c s reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (atom_first_zero_env k rows base a (b+n) c s (reserve ++ List.replicate n 0)))
  simpa using h

theorem atom_first_c_cycle (k : Nat) (rows : AtomFirstLookupRows k) (base : RegisterMachine.Bank 9)
    (env a b c s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgEnv (k+26) base env a b (c+1) s reserve) 3
      (cfgEnv (k+26) base (env+1) a b c s (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (atom_first_dec_c k rows base env a b c s reserve)
  have h2 := WordEventSystem.Block.single graphSystem (atom_first_inc_env k rows base env a b c s (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (atom_first_jump_c k rows base (env+1) a b c s (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem atom_first_c_many (n k : Nat) (rows : AtomFirstLookupRows k) (base : RegisterMachine.Bank 9)
    (env a b s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgEnv (k+26) base env a b n s reserve) (3*n)
      (cfgEnv (k+26) base (env+n) a b 0 s (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing env reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgEnv (k+26) base env a b 0 s reserve)
  | succ n ih =>
    have h := (atom_first_c_cycle k rows base env a b n s reserve).trans graphSystem (ih (env+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem atom_first_c_move (n k : Nat) (rows : AtomFirstLookupRows k) (base : RegisterMachine.Bank 9)
    (env a b s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgEnv (k+26) base env a b n s reserve) (3*n+1)
      (cfgEnv (k+29) base (env+n) a b 0 s (reserve ++ List.replicate n 0)) [] := by
  have h := (atom_first_c_many n k rows base env a b s reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (atom_first_zero_c k rows base (env+n) a b s (reserve ++ List.replicate n 0)))
  simpa using h

/-- From a prepared atom lookup entry, save the low-index operand in env and
retain the exact following environment tail in scratch. This is a silent
finite graph computation, not yet evaluation of the whole atomic formula. -/
theorem atom_first_lookup (index encoded k : Nat) (rows : AtomFirstLookupRows k)
    (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgEnv k base encoded index 0 0 0 reserve) duration
        (cfgEnv (k+29) base (M236Game.lookup encoded index) 0 0 0
          (Cantor.unpair (environmentTail encoded index)).2 (reserve ++ List.replicate padding 0)) [] := by
  have h1 := atom_first_env_move encoded k rows base index 0 0 0 reserve
  simp only [Nat.zero_add] at h1
  obtain ⟨scanDuration, scanPadding, ht, h2⟩ := environment_scan index encoded (k+3) rows.scan
    (RegisterMachine.write base 5 0) (reserve ++ List.replicate encoded 0)
  change graphSystem.Block (cfgEnv (k+3) base 0 index encoded 0 0 (reserve ++ List.replicate encoded 0)) scanDuration
    (cfgEnv (k+26) base 0 0 0 (M236Game.lookup encoded index)
      (Cantor.unpair (environmentTail encoded index)).2
      ((reserve ++ List.replicate encoded 0) ++ List.replicate scanPadding 0)) [] at h2
  have h3 := atom_first_c_move (M236Game.lookup encoded index) k rows base 0 0 0
    (Cantor.unpair (environmentTail encoded index)).2
    ((reserve ++ List.replicate encoded 0) ++ List.replicate scanPadding 0)
  simp only [Nat.zero_add] at h3
  have h := (h1.trans graphSystem h2).trans graphSystem h3
  refine ⟨3*encoded+1+scanDuration+(3*M236Game.lookup encoded index+1),
    encoded+scanPadding+M236Game.lookup encoded index, by omega, ?_⟩
  have hr : ((reserve ++ List.replicate encoded 0) ++ List.replicate scanPadding 0) ++
      List.replicate (M236Game.lookup encoded index) 0 =
        reserve ++ List.replicate (encoded+scanPadding+M236Game.lookup encoded index) 0 := by
    simp only [List.replicate_add, List.append_assoc]
  simp only [List.nil_append] at h
  rw [hr] at h
  exact h


def cfgAtom (i : Nat) (base : RegisterMachine.Bank 9) (top env a b c scratch : Nat)
    (reserve : List Nat) : GraphState :=
  cfgEnv i (RegisterMachine.write base 4 top) env a b c scratch reserve

/-- The remaining atomic lookup reads from the saved tail, retains the first
operand in env and transfers both operands into a and b. -/
structure AtomSecondLookupRows (k : Nat) : Prop where
  decS : sourceRows[k]? = some ("3.scratch.copy.decnz", k+1, some (k+3))
  incB : sourceRows[k+1]? = some ("3.k.b.inc", k+2, none)
  jumpS : sourceRows[k+2]? = some ("jump", k, none)
  decTop : sourceRows[k+3]? = some ("3.k.top.decnz", k+4, some (k+6))
  incA : sourceRows[k+4]? = some ("3.k.a.inc", k+5, none)
  jumpTop : sourceRows[k+5]? = some ("jump", k+3, none)
  scan : EnvironmentLookupRows (k+6)
  clearS : sourceRows[k+29]? = some ("3.scratch.copy.decnz", k+30, some (k+31))
  jumpClear : sourceRows[k+30]? = some ("jump", k+29, none)
  decC : sourceRows[k+31]? = some ("3.k.c.decnz", k+32, some (k+34))
  incBAgain : sourceRows[k+32]? = some ("3.k.b.inc", k+33, none)
  jumpC : sourceRows[k+33]? = some ("jump", k+31, none)
  decEnv : sourceRows[k+34]? = some ("3.k.env.decnz", k+35, some (k+37))
  incAAgain : sourceRows[k+35]? = some ("3.k.a.inc", k+36, none)
  jumpEnv : sourceRows[k+36]? = some ("jump", k+34, none)

theorem atom_second_lookup_rows_299 : AtomSecondLookupRows 299 := by constructor <;> first | constructor <;> constructor <;> decide
theorem atom_second_lookup_rows_476 : AtomSecondLookupRows 476 := by constructor <;> first | constructor <;> constructor <;> decide
theorem atom_second_lookup_rows_656 : AtomSecondLookupRows 656 := by constructor <;> first | constructor <;> constructor <;> decide

theorem atom2_s_b_dec (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom k base top env a b c (s+1) reserve) = (cfgAtom (k+1) base top env a b c s (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.decS, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom2_s_b_zero (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c _s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom k base top env a b c 0 reserve) = (cfgAtom (k+3) base top env a b c 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.decS, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem atom2_s_b_inc (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+1) base top env a b c s reserve) = (cfgAtom (k+2) base top env a (b+1) c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.incB, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom2_s_b_jump (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+2) base top env a b c s reserve) = (cfgAtom k base top env a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.jumpS, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem atom2_s_b_cycle (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAtom k base top env a b c (s+1) reserve) 3 (cfgAtom k base top env a (b+1) c s (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (atom2_s_b_dec k rows base top env a b c s reserve)
  have h2 := WordEventSystem.Block.single graphSystem (atom2_s_b_inc k rows base top env a b c s (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (atom2_s_b_jump k rows base top env a (b+1) c s (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem atom2_s_b_many (n k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAtom k base top env a b c n reserve) (3*n)
      (cfgAtom k base top env a (b+n) c 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing b reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgAtom k base top env a b c 0 reserve)
  | succ n ih =>
    have h := (atom2_s_b_cycle k rows base top env a b c n reserve).trans graphSystem (ih (b+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem atom2_s_b_move (n k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAtom k base top env a b c n reserve) (3*n+1)
      (cfgAtom (k+3) base top env a (b+n) c 0 (reserve ++ List.replicate n 0)) [] := by
  have h := (atom2_s_b_many n k rows base top env a b c reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (atom2_s_b_zero k rows base top env a (b+n) c 0 (reserve ++ List.replicate n 0)))
  simpa using h

theorem atom2_top_a_dec (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+3) base (top+1) env a b c s reserve) = (cfgAtom (k+4) base top env a b c s (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.decTop, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom2_top_a_zero (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (_top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+3) base 0 env a b c s reserve) = (cfgAtom (k+6) base 0 env a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.decTop, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute, RegisterMachine.write]

theorem atom2_top_a_inc (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+4) base top env a b c s reserve) = (cfgAtom (k+5) base top env (a+1) b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.incA, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom2_top_a_jump (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+5) base top env a b c s reserve) = (cfgAtom (k+3) base top env a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.jumpTop, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem atom2_top_a_cycle (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAtom (k+3) base (top+1) env a b c s reserve) 3 (cfgAtom (k+3) base top env (a+1) b c s (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (atom2_top_a_dec k rows base top env a b c s reserve)
  have h2 := WordEventSystem.Block.single graphSystem (atom2_top_a_inc k rows base top env a b c s (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (atom2_top_a_jump k rows base top env (a+1) b c s (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem atom2_top_a_many (n k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (env a b c s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAtom (k+3) base n env a b c s reserve) (3*n)
      (cfgAtom (k+3) base 0 env (a+n) b c s (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing a reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgAtom (k+3) base 0 env a b c s reserve)
  | succ n ih =>
    have h := (atom2_top_a_cycle k rows base n env a b c s reserve).trans graphSystem (ih (a+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem atom2_top_a_move (n k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (env a b c s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAtom (k+3) base n env a b c s reserve) (3*n+1)
      (cfgAtom (k+6) base 0 env (a+n) b c s (reserve ++ List.replicate n 0)) [] := by
  have h := (atom2_top_a_many n k rows base env a b c s reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (atom2_top_a_zero k rows base 0 env (a+n) b c s (reserve ++ List.replicate n 0)))
  simpa using h

theorem atom2_c_b_dec (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+31) base top env a b (c+1) s reserve) = (cfgAtom (k+32) base top env a b c s (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.decC, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom2_c_b_zero (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b _c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+31) base top env a b 0 s reserve) = (cfgAtom (k+34) base top env a b 0 s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.decC, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem atom2_c_b_inc (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+32) base top env a b c s reserve) = (cfgAtom (k+33) base top env a (b+1) c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.incBAgain, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom2_c_b_jump (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+33) base top env a b c s reserve) = (cfgAtom (k+31) base top env a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.jumpC, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem atom2_c_b_cycle (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAtom (k+31) base top env a b (c+1) s reserve) 3 (cfgAtom (k+31) base top env a (b+1) c s (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (atom2_c_b_dec k rows base top env a b c s reserve)
  have h2 := WordEventSystem.Block.single graphSystem (atom2_c_b_inc k rows base top env a b c s (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (atom2_c_b_jump k rows base top env a (b+1) c s (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem atom2_c_b_many (n k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAtom (k+31) base top env a b n s reserve) (3*n)
      (cfgAtom (k+31) base top env a (b+n) 0 s (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing b reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgAtom (k+31) base top env a b 0 s reserve)
  | succ n ih =>
    have h := (atom2_c_b_cycle k rows base top env a b n s reserve).trans graphSystem (ih (b+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem atom2_c_b_move (n k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAtom (k+31) base top env a b n s reserve) (3*n+1)
      (cfgAtom (k+34) base top env a (b+n) 0 s (reserve ++ List.replicate n 0)) [] := by
  have h := (atom2_c_b_many n k rows base top env a b s reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (atom2_c_b_zero k rows base top env a (b+n) 0 s (reserve ++ List.replicate n 0)))
  simpa using h

theorem atom2_env_a_dec (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+34) base top (env+1) a b c s reserve) = (cfgAtom (k+35) base top env a b c s (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.decEnv, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom2_env_a_zero (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top _env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+34) base top 0 a b c s reserve) = (cfgAtom (k+37) base top 0 a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.decEnv, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem atom2_env_a_inc (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+35) base top env a b c s reserve) = (cfgAtom (k+36) base top env (a+1) b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.incAAgain, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom2_env_a_jump (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+36) base top env a b c s reserve) = (cfgAtom (k+34) base top env a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.jumpEnv, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem atom2_env_a_cycle (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAtom (k+34) base top (env+1) a b c s reserve) 3 (cfgAtom (k+34) base top env (a+1) b c s (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (atom2_env_a_dec k rows base top env a b c s reserve)
  have h2 := WordEventSystem.Block.single graphSystem (atom2_env_a_inc k rows base top env a b c s (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (atom2_env_a_jump k rows base top env (a+1) b c s (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem atom2_env_a_many (n k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top a b c s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAtom (k+34) base top n a b c s reserve) (3*n)
      (cfgAtom (k+34) base top 0 (a+n) b c s (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing a reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgAtom (k+34) base top 0 a b c s reserve)
  | succ n ih =>
    have h := (atom2_env_a_cycle k rows base top n a b c s reserve).trans graphSystem (ih (a+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem atom2_env_a_move (n k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top a b c s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAtom (k+34) base top n a b c s reserve) (3*n+1)
      (cfgAtom (k+37) base top 0 (a+n) b c s (reserve ++ List.replicate n 0)) [] := by
  have h := (atom2_env_a_many n k rows base top a b c s reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (atom2_env_a_zero k rows base top 0 (a+n) b c s (reserve ++ List.replicate n 0)))
  simpa using h


theorem atom2_clear_s_dec (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+29) base top env a b c (s+1) reserve) =
      (cfgAtom (k+30) base top env a b c s (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.clearS, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem atom2_clear_s_zero (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+29) base top env a b c 0 reserve) =
      (cfgAtom (k+31) base top env a b c 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.clearS, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem atom2_clear_s_jump (k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAtom (k+30) base top env a b c s reserve) =
      (cfgAtom (k+29) base top env a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgAtom, cfgEnv, cfgHalf, rows.jumpClear, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem atom2_clear_s_many (n k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAtom (k+29) base top env a b c n reserve) (2*n)
      (cfgAtom (k+29) base top env a b c 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgAtom (k+29) base top env a b c 0 reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (atom2_clear_s_dec k rows base top env a b c n reserve)
    have h2 := WordEventSystem.Block.single graphSystem (atom2_clear_s_jump k rows base top env a b c n (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem atom2_clear_s (n k : Nat) (rows : AtomSecondLookupRows k) (base : RegisterMachine.Bank 9)
    (top env a b c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAtom (k+29) base top env a b c n reserve) (2*n+1)
      (cfgAtom (k+31) base top env a b c 0 (reserve ++ List.replicate n 0)) [] := by
  have h := (atom2_clear_s_many n k rows base top env a b c reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem
      (atom2_clear_s_zero k rows base top env a b c (reserve ++ List.replicate n 0)))
  simpa using h

theorem environment_tail_add (e n m : Nat) :
    environmentTail e (n+m) = environmentTail (environmentTail e n) m := by
  induction n generalizing e with
  | zero => simp [environmentTail]
  | succ n ih => simpa [environmentTail, Nat.succ_add] using ih (Cantor.unpair e).2

theorem environment_tail_succ (e n : Nat) :
    environmentTail e (n+1) = (Cantor.unpair (environmentTail e n)).2 := by
  rw [environment_tail_add]
  rfl

/-- Looking up g positions in the tail following j is lookup at j+g+1 in
the original encoded environment, including exhausted zero tails. -/
theorem lookup_after_selected_tail (e j g : Nat) :
    M236Game.lookup (Cantor.unpair (environmentTail e j)).2 g = M236Game.lookup e (j+g+1) := by
  rw [← environment_tail_lookup, ← environment_tail_lookup]
  have h : j+g+1 = (j+1)+g := by omega
  rw [h, environment_tail_add, environment_tail_succ]

/-- From the prepared second lookup entry, put the low-index operand in a and
the value g positions into its following tail in b. No bit is tested here. -/
theorem atom_second_lookup (gap low tail k : Nat) (rows : AtomSecondLookupRows k)
    (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgAtom k base gap low 0 0 0 tail reserve) duration
        (cfgAtom (k+37) base 0 0 low (M236Game.lookup tail gap) 0 0
          (reserve ++ List.replicate padding 0)) [] := by
  let high := M236Game.lookup tail gap
  let extra := (Cantor.unpair (environmentTail tail gap)).2
  have h1 := atom2_s_b_move tail k rows base gap low 0 0 0 reserve
  simp only [Nat.zero_add] at h1
  have h2 := atom2_top_a_move gap k rows base low 0 tail 0 0 (reserve ++ List.replicate tail 0)
  simp only [Nat.zero_add] at h2
  obtain ⟨scanDuration, scanPadding, ht, h3⟩ := environment_scan gap tail (k+6) rows.scan
    (RegisterMachine.write (RegisterMachine.write base 4 0) 5 low)
    ((reserve ++ List.replicate tail 0) ++ List.replicate gap 0)
  change graphSystem.Block (cfgAtom (k+6) base 0 low gap tail 0 0
      ((reserve ++ List.replicate tail 0) ++ List.replicate gap 0)) scanDuration
    (cfgAtom (k+29) base 0 low 0 0 high extra
      (((reserve ++ List.replicate tail 0) ++ List.replicate gap 0) ++ List.replicate scanPadding 0)) [] at h3
  have h4 := atom2_clear_s extra k rows base 0 low 0 0 high
    (((reserve ++ List.replicate tail 0) ++ List.replicate gap 0) ++ List.replicate scanPadding 0)
  have h5 := atom2_c_b_move high k rows base 0 low 0 0 0
    ((((reserve ++ List.replicate tail 0) ++ List.replicate gap 0) ++ List.replicate scanPadding 0) ++ List.replicate extra 0)
  simp only [Nat.zero_add] at h5
  have h6 := atom2_env_a_move low k rows base 0 0 high 0 0
    (((((reserve ++ List.replicate tail 0) ++ List.replicate gap 0) ++ List.replicate scanPadding 0) ++ List.replicate extra 0) ++ List.replicate high 0)
  simp only [Nat.zero_add] at h6
  have h := (((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5).trans graphSystem h6)
  refine ⟨3*tail+1+(3*gap+1)+scanDuration+(2*extra+1)+(3*high+1)+(3*low+1),
    tail+gap+scanPadding+extra+high+low, by omega, ?_⟩
  have hr : (((((reserve ++ List.replicate tail 0) ++ List.replicate gap 0) ++ List.replicate scanPadding 0) ++
      List.replicate extra 0) ++ List.replicate high 0) ++ List.replicate low 0 =
        reserve ++ List.replicate (tail+gap+scanPadding+extra+high+low) 0 := by
    simp only [List.replicate_add, List.append_assoc]
  simp only [List.nil_append] at h
  rw [hr] at h
  exact h

/-- Both prepared lookups place the bit index in a and the container in b.
The following bit-extraction block is separate and is not assumed here. -/
theorem atom_lookup_operands (index gap encoded k : Nat)
    (first : AtomFirstLookupRows k) (second : AtomSecondLookupRows (k+29))
    (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgAtom k base gap encoded index 0 0 0 reserve) duration
        (cfgAtom (k+66) base 0 0 (M236Game.lookup encoded index)
          (M236Game.lookup encoded (index+gap+1)) 0 0
          (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨firstDuration, firstPadding, hf, h1⟩ := atom_first_lookup index encoded k first
    (RegisterMachine.write base 4 gap) reserve
  change graphSystem.Block (cfgAtom k base gap encoded index 0 0 0 reserve) firstDuration
    (cfgAtom (k+29) base gap (M236Game.lookup encoded index) 0 0 0
      (Cantor.unpair (environmentTail encoded index)).2 (reserve ++ List.replicate firstPadding 0)) [] at h1
  obtain ⟨duration, padding, ht, h2⟩ := atom_second_lookup gap (M236Game.lookup encoded index)
    (Cantor.unpair (environmentTail encoded index)).2 (k+29) second base
    (reserve ++ List.replicate firstPadding 0)
  simp only [Nat.add_assoc, lookup_after_selected_tail] at h2
  have h := h1.trans graphSystem h2
  refine ⟨firstDuration+duration, firstPadding+padding, by omega, ?_⟩
  have hr : (reserve ++ List.replicate firstPadding 0) ++ List.replicate padding 0 =
      reserve ++ List.replicate (firstPadding+padding) 0 := by
    simp only [List.replicate_add, List.append_assoc]
  simp only [List.nil_append] at h
  rw [hr] at h
  exact h

/-- The prepared operands have exactly the bit meaning of the mathematical
strict ordered atom. This does not itself execute the later bit test. -/
theorem atom_lookup_operand_meaning (payload encoded : Nat) :
    (M236Game.lookup encoded ((Cantor.unpair payload).1 + (Cantor.unpair payload).2 + 1)).testBit
        (M236Game.lookup encoded (Cantor.unpair payload).1) = M236Game.encodedAtom payload encoded := by
  rfl

/-- Physical lift from an explicitly reached prepared operand-lookup entry. -/
theorem selected_atom_lookup_operands (i index gap encoded k : Nat)
    (first : AtomFirstLookupRows k) (second : AtomSecondLookupRows (k+29))
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (h : graphSystem.run i = cfgAtom k base gap encoded index 0 0 0 reserve) :
    ∃ duration padding finish, 0 < duration ∧ Good finish ∧
      finish.graphState = cfgAtom (k+66) base 0 0 (M236Game.lookup encoded index)
        (M236Game.lookup encoded (index+gap+1)) 0 0 (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgAtom (k+66) base 0 0 (M236Game.lookup encoded index)
        (M236Game.lookup encoded (index+gap+1)) 0 0 (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := atom_lookup_operands index gap encoded k first second base reserve
  have hr : graphSystem.run (i+duration) = cfgAtom (k+66) base 0 0 (M236Game.lookup encoded index)
      (M236Game.lookup encoded (index+gap+1)) 0 0 (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
