import PASoundness.M236FormulaScan
import PASoundness.M236Game

/-! Prepared numeric-environment scan used by the atomic evaluator. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

/-- The `scan_to_a` shape: an initial unpair followed by zero or more
clear/move/unpair rounds, with the selected head in c and tail in scratch. -/
structure EnvironmentLookupRows (k : Nat) : Prop where
  first : FormulaScanRows k
  later : FormulaScanRows (k+14)
  decA : sourceRows[k+8]? = some ("3.k.a.decnz", k+9, some (k+23))
  clearC : sourceRows[k+9]? = some ("3.k.c.decnz", k+10, some (k+11))
  clearJump : sourceRows[k+10]? = some ("jump", k+9, none)
  decScratch : sourceRows[k+11]? = some ("3.scratch.copy.decnz", k+12, some (k+14))
  incB : sourceRows[k+12]? = some ("3.k.b.inc", k+13, none)
  moveJump : sourceRows[k+13]? = some ("jump", k+11, none)
  repeatJump : sourceRows[k+22]? = some ("jump", k+8, none)

theorem environment_lookup_rows_273 : EnvironmentLookupRows 273 := by constructor <;> constructor <;> decide
theorem environment_lookup_rows_305 : EnvironmentLookupRows 305 := by constructor <;> constructor <;> decide
theorem environment_lookup_rows_450 : EnvironmentLookupRows 450 := by constructor <;> constructor <;> decide
theorem environment_lookup_rows_482 : EnvironmentLookupRows 482 := by constructor <;> constructor <;> decide
theorem environment_lookup_rows_630 : EnvironmentLookupRows 630 := by constructor <;> constructor <;> decide
theorem environment_lookup_rows_662 : EnvironmentLookupRows 662 := by constructor <;> constructor <;> decide

def environmentTail : Nat → Nat → Nat
  | e, 0 => e
  | e, n+1 => environmentTail (Cantor.unpair e).2 n

theorem environment_tail_zero (n : Nat) : environmentTail 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [environmentTail, Cantor.unpair, Cantor.unpairAux] using ih

/-- Taking the head after walking n encoded tails is exactly the source-level
lookup, including the zero tail and its default-zero convention. -/
theorem environment_tail_lookup (e n : Nat) :
    (Cantor.unpair (environmentTail e n)).1 = M236Game.lookup e n := by
  induction n generalizing e with
  | zero =>
    by_cases h : e = 0
    · subst e; simp [environmentTail, M236Game.lookup, Cantor.unpair, Cantor.unpairAux]
    · simp [environmentTail, M236Game.lookup, h]
  | succ n ih =>
    by_cases h : e = 0
    · subst e; simp [environment_tail_zero, M236Game.lookup, Cantor.unpair, Cantor.unpairAux]
    · simpa [environmentTail, M236Game.lookup, h] using ih (Cantor.unpair e).2

theorem env_scan_dec_a (k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+8) base (a+1) b c s reserve) =
      (cfgHalf (k+9) base a b c s (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.decA, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem env_scan_zero_a (k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+8) base 0 b c s reserve) =
      (cfgHalf (k+23) base 0 b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.decA, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem env_scan_dec_c (k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+9) base a b (c+1) s reserve) =
      (cfgHalf (k+10) base a b c s (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.clearC, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem env_scan_zero_c (k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+9) base a b 0 s reserve) =
      (cfgHalf (k+11) base a b 0 s reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.clearC, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem env_scan_jump_c (k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+10) base a b c s reserve) = (cfgHalf (k+9) base a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.clearJump, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem env_scan_dec_s (k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+11) base a b c (s+1) reserve) =
      (cfgHalf (k+12) base a b c s (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.decScratch, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem env_scan_zero_s (k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+11) base a b c 0 reserve) =
      (cfgHalf (k+14) base a b c 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.decScratch, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]

theorem env_scan_inc_b (k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+12) base a b c s reserve) = (cfgHalf (k+13) base a (b+1) c s reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.incB, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankHalf, RegisterMachine.execute]
  all_goals (funext i; fin_cases i <;> simp [bankHalf, RegisterMachine.write])

theorem env_scan_jump_s (k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+13) base a b c s reserve) = (cfgHalf (k+11) base a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.moveJump, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem env_scan_jump_repeat (k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c s : Nat) (reserve : List Nat) :
    graphSystem.step (cfgHalf (k+22) base a b c s reserve) = (cfgHalf (k+8) base a b c s reserve, []) := by
  simp [graphSystem, graphNext, cfgHalf, rows.repeatJump, nextIndex, nextBank, nextReserve, incRegister, decRegister, outputForOp]

theorem env_scan_clear_cycle (k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+9) base a b (c+1) s reserve) 2
      (cfgHalf (k+9) base a b c s (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (env_scan_dec_c k rows base a b c s reserve)
  have h2 := WordEventSystem.Block.single graphSystem (env_scan_jump_c k rows base a b c s (reserve ++ [0]))
  simpa using h1.trans graphSystem h2

theorem env_scan_clear_many (n k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+9) base a b n s reserve) (2*n)
      (cfgHalf (k+9) base a b 0 s (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgHalf (k+9) base a b 0 s reserve)
  | succ n ih =>
    have h := (env_scan_clear_cycle k rows base a b n s reserve).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem env_scan_clear (n k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+9) base a b n s reserve) (2*n+1)
      (cfgHalf (k+11) base a b 0 s (reserve ++ List.replicate n 0)) [] := by
  have h := (env_scan_clear_many n k rows base a b s reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (env_scan_zero_c k rows base a b s (reserve ++ List.replicate n 0)))
  simpa using h

theorem env_scan_move_cycle (k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c s : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+11) base a b c (s+1) reserve) 3
      (cfgHalf (k+11) base a (b+1) c s (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (env_scan_dec_s k rows base a b c s reserve)
  have h2 := WordEventSystem.Block.single graphSystem (env_scan_inc_b k rows base a b c s (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (env_scan_jump_s k rows base a (b+1) c s (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem env_scan_move_many (n k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+11) base a b c n reserve) (3*n)
      (cfgHalf (k+11) base a (b+n) c 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing b reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgHalf (k+11) base a b c 0 reserve)
  | succ n ih =>
    have h := (env_scan_move_cycle k rows base a b c n reserve).trans graphSystem (ih (b+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem env_scan_move (n k : Nat) (rows : EnvironmentLookupRows k) (base : RegisterMachine.Bank 9)
    (a b c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgHalf (k+11) base a b c n reserve) (3*n+1)
      (cfgHalf (k+14) base a (b+n) c 0 (reserve ++ List.replicate n 0)) [] := by
  have h := (env_scan_move_many n k rows base a b c reserve).trans graphSystem
    (WordEventSystem.Block.single graphSystem (env_scan_zero_s k rows base a (b+n) c (reserve ++ List.replicate n 0)))
  simpa using h

/-- Once the current encoded node has been unpaired, walk n further tails.
This is a prepared local graph block; it does not assert evaluator reachability. -/
theorem environment_scan_loop (n e k : Nat) (rows : EnvironmentLookupRows k)
    (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgHalf (k+8) base n 0 (Cantor.unpair e).1 (Cantor.unpair e).2 reserve) duration
        (cfgHalf (k+23) base 0 0 (Cantor.unpair (environmentTail e n)).1
          (Cantor.unpair (environmentTail e n)).2 (reserve ++ List.replicate padding 0)) [] := by
  induction n generalizing e reserve with
  | zero =>
    refine ⟨1, 0, by omega, ?_⟩
    simpa [environmentTail] using WordEventSystem.Block.single graphSystem
      (env_scan_zero_a k rows base 0 (Cantor.unpair e).1 (Cantor.unpair e).2 reserve)
  | succ n ih =>
    let head := (Cantor.unpair e).1
    let tail := (Cantor.unpair e).2
    have h1 := WordEventSystem.Block.single graphSystem (env_scan_dec_a k rows base n 0 head tail reserve)
    have h2 := env_scan_clear head k rows base n 0 tail (reserve ++ [0])
    have h3 := env_scan_move tail k rows base n 0 0 ((reserve ++ [0]) ++ List.replicate head 0)
    simp only [Nat.zero_add] at h3
    obtain ⟨scanDuration, scanPadding, hscan, h4⟩ := formula_diagonal_unpair n tail (k+14) rows.later base
      (((reserve ++ [0]) ++ List.replicate head 0) ++ List.replicate tail 0)
    have h5 := WordEventSystem.Block.single graphSystem
      (env_scan_jump_repeat k rows base n 0 (Cantor.unpair tail).1 (Cantor.unpair tail).2
        ((((reserve ++ [0]) ++ List.replicate head 0) ++ List.replicate tail 0) ++ List.replicate scanPadding 0))
    simp only [Nat.add_assoc] at h4
    obtain ⟨duration, padding, ht, h6⟩ := ih tail
      ((((reserve ++ [0]) ++ List.replicate head 0) ++ List.replicate tail 0) ++ List.replicate scanPadding 0)
    have h := (((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5).trans graphSystem h6)
    refine ⟨1+(2*head+1)+(3*tail+1)+scanDuration+1+duration,
      1+head+tail+scanPadding+padding, by omega, ?_⟩
    have hr : ((((reserve ++ [0]) ++ List.replicate head 0) ++ List.replicate tail 0) ++
        List.replicate scanPadding 0) ++ List.replicate padding 0 =
        reserve ++ List.replicate (1+head+tail+scanPadding+padding) 0 := by
      simp only [List.replicate_add, List.replicate_succ, List.replicate_zero, List.append_assoc]
    simp only [List.nil_append] at h
    rw [hr] at h
    simpa only [environmentTail, head, tail] using h

/-- Exact prepared scan: the numerical environment is consumed from `b`,
the requested index from `a`, and `c` receives the mathematical lookup.
Scratch retains the unused tail. Other registers are preserved, no events
are emitted, and reserve growth is finite and all-zero. -/
theorem environment_scan (index e k : Nat) (rows : EnvironmentLookupRows k)
    (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, 0 < duration ∧
      graphSystem.Block (cfgHalf k base index e 0 0 reserve) duration
        (cfgHalf (k+23) base 0 0 (M236Game.lookup e index)
          (Cantor.unpair (environmentTail e index)).2 (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨firstDuration, firstPadding, hfirst, h1⟩ := formula_diagonal_unpair index e k rows.first base reserve
  obtain ⟨duration, padding, ht, h2⟩ := environment_scan_loop index e k rows base
    (reserve ++ List.replicate firstPadding 0)
  have h := h1.trans graphSystem h2
  refine ⟨firstDuration+duration, firstPadding+padding, by omega, ?_⟩
  have hr : (reserve ++ List.replicate firstPadding 0) ++ List.replicate padding 0 =
      reserve ++ List.replicate (firstPadding+padding) 0 := by
    simp only [List.replicate_add, List.append_assoc]
  simp only [List.nil_append] at h
  rw [hr, environment_tail_lookup] at h
  exact h

/-- Physical lift at an explicitly reached prepared scan entry. -/
theorem selected_environment_scan (i index e k : Nat) (rows : EnvironmentLookupRows k)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (h : graphSystem.run i = cfgHalf k base index e 0 0 reserve) :
    ∃ duration padding finish, 0 < duration ∧ Good finish ∧
      finish.graphState = cfgHalf (k+23) base 0 0 (M236Game.lookup e index)
        (Cantor.unpair (environmentTail e index)).2 (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgHalf (k+23) base 0 0 (M236Game.lookup e index)
        (Cantor.unpair (environmentTail e index)).2 (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := environment_scan index e k rows base reserve
  have hr : graphSystem.run (i+duration) = cfgHalf (k+23) base 0 0 (M236Game.lookup e index)
      (Cantor.unpair (environmentTail e index)).2 (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
