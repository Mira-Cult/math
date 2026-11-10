import PASoundness.M236GenericUnpair

/-! Shared unary-output routine for the checked occurrence graph. The schema
preserves every register other than `a` and scratch, emits exactly the unary
word, and restores those two registers. Reachability is a separate hypothesis. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

structure EmitRows (k : Nat) : Prop where
  decA : sourceRows[k]? = some ("3.k.a.decnz", k+1, some (k+4))
  one : sourceRows[k+1]? = some ("emit.1", k+2, none)
  incScratch : sourceRows[k+2]? = some ("3.scratch.copy.inc", k+3, none)
  jumpEmit : sourceRows[k+3]? = some ("jump", k, none)
  zero : sourceRows[k+4]? = some ("emit.0", k+5, none)
  decScratch : sourceRows[k+5]? = some ("3.scratch.copy.decnz", k+6, some (k+8))
  incA : sourceRows[k+6]? = some ("3.k.a.inc", k+7, none)
  jumpRestore : sourceRows[k+7]? = some ("jump", k+5, none)

theorem emit_rows_19 : EmitRows 19 := by constructor <;> decide
theorem emit_rows_41 : EmitRows 41 := by constructor <;> decide
theorem emit_rows_68 : EmitRows 68 := by constructor <;> decide
theorem emit_rows_95 : EmitRows 95 := by constructor <;> decide

theorem generic_emit_dec_a (k : Nat) (rows : EmitRows k) (base : RegisterMachine.Bank 9) (n scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS k base (n+1) scratch reserve) = (cfgAS (k+1) base n scratch (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAS, rows.decA, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAS, RegisterMachine.write])

theorem generic_emit_zero_a (k : Nat) (rows : EmitRows k) (base : RegisterMachine.Bank 9) (scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS k base 0 scratch reserve) = (cfgAS (k+4) base 0 scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, rows.decA, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute, RegisterMachine.write]

theorem generic_emit_one (k : Nat) (rows : EmitRows k) (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS (k+1) base a scratch reserve) = (cfgAS (k+2) base a scratch reserve, [true]) := by
  simp [graphSystem, graphNext, cfgAS, rows.one, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem generic_emit_inc_scratch (k : Nat) (rows : EmitRows k) (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS (k+2) base a scratch reserve) = (cfgAS (k+3) base a (scratch+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, rows.incScratch, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAS, RegisterMachine.write])

theorem generic_emit_jump_out (k : Nat) (rows : EmitRows k) (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS (k+3) base a scratch reserve) = (cfgAS k base a scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, rows.jumpEmit, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem generic_emit_zero (k : Nat) (rows : EmitRows k) (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS (k+4) base a scratch reserve) = (cfgAS (k+5) base a scratch reserve, [false]) := by
  simp [graphSystem, graphNext, cfgAS, rows.zero, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem generic_emit_dec_scratch (k : Nat) (rows : EmitRows k) (base : RegisterMachine.Bank 9) (a n : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS (k+5) base a (n+1) reserve) = (cfgAS (k+6) base a n (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAS, rows.decScratch, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAS, RegisterMachine.write])

theorem generic_emit_zero_scratch (k : Nat) (rows : EmitRows k) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS (k+5) base a 0 reserve) = (cfgAS (k+8) base a 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, rows.decScratch, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute, RegisterMachine.write]

theorem generic_emit_inc_a (k : Nat) (rows : EmitRows k) (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS (k+6) base a scratch reserve) = (cfgAS (k+7) base (a+1) scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, rows.incA, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAS, RegisterMachine.write])

theorem generic_emit_jump_restore (k : Nat) (rows : EmitRows k) (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS (k+7) base a scratch reserve) = (cfgAS (k+5) base a scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, rows.jumpRestore, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem generic_emit_cycle (k : Nat) (rows : EmitRows k) (base : RegisterMachine.Bank 9) (n scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAS k base (n+1) scratch reserve) 4
      (cfgAS k base n (scratch+1) (reserve ++ [0])) [true] := by
  have h1 := WordEventSystem.Block.single graphSystem (generic_emit_dec_a k rows base n scratch reserve)
  have h2 := WordEventSystem.Block.single graphSystem (generic_emit_one k rows base n scratch (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (generic_emit_inc_scratch k rows base n scratch (reserve ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (generic_emit_jump_out k rows base n (scratch+1) (reserve ++ [0]))
  simpa using ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4

theorem generic_emit_many (k : Nat) (rows : EmitRows k) (n : Nat) (base : RegisterMachine.Bank 9) (scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAS k base n scratch reserve) (4*n)
      (cfgAS k base 0 (scratch+n) (reserve ++ List.replicate n 0)) (List.replicate n true) := by
  induction n generalizing scratch reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgAS k base 0 scratch reserve)
  | succ n ih =>
    have h := (generic_emit_cycle k rows base n scratch reserve).trans graphSystem (ih (scratch+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem generic_emit_restore_a_cycle (k : Nat) (rows : EmitRows k) (base : RegisterMachine.Bank 9) (a n : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAS (k+5) base a (n+1) reserve) 3
      (cfgAS (k+5) base (a+1) n (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (generic_emit_dec_scratch k rows base a n reserve)
  have h2 := WordEventSystem.Block.single graphSystem (generic_emit_inc_a k rows base a n (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (generic_emit_jump_restore k rows base (a+1) n (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem generic_emit_restore_a_all (k : Nat) (rows : EmitRows k) (n : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAS (k+5) base a n reserve) (3*n)
      (cfgAS (k+5) base (a+n) 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing a reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgAS (k+5) base a 0 reserve)
  | succ n ih =>
    have h := (generic_emit_restore_a_cycle k rows base a n reserve).trans graphSystem (ih (a+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- Emit the natural in unary, restore a and clear initially zero scratch. -/
theorem generic_emit_preserving_a (k : Nat) (rows : EmitRows k) (n : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    graphSystem.Block (cfgAS k base n 0 reserve) (7*n+3)
      (cfgAS (k+8) base n 0 ((reserve ++ List.replicate n 0) ++ List.replicate n 0))
      (List.replicate n true ++ [false]) := by
  have h1 : graphSystem.Block (cfgAS k base n 0 reserve) (4*n)
      (cfgAS k base 0 n (reserve ++ List.replicate n 0)) (List.replicate n true) := by
    simpa only [Nat.zero_add] using generic_emit_many k rows n base 0 reserve
  have h2 := WordEventSystem.Block.single graphSystem (generic_emit_zero_a k rows base n (reserve ++ List.replicate n 0))
  have h3 := WordEventSystem.Block.single graphSystem (generic_emit_zero k rows base 0 n (reserve ++ List.replicate n 0))
  have h4 : graphSystem.Block (cfgAS (k+5) base 0 n (reserve ++ List.replicate n 0)) (3*n)
      (cfgAS (k+5) base n 0 ((reserve ++ List.replicate n 0) ++ List.replicate n 0)) [] := by
    simpa only [Nat.zero_add] using generic_emit_restore_a_all k rows n base 0 (reserve ++ List.replicate n 0)
  have h5 := WordEventSystem.Block.single graphSystem
    (generic_emit_zero_scratch k rows base n ((reserve ++ List.replicate n 0) ++ List.replicate n 0))
  have h := (((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5
  have ht : 4*n+1+1+3*n+1 = 7*n+3 := by omega
  simpa [ht] using h

/-- At any reached checked occurrence, the selected physical execution emits
exactly the unary field and advances by positive physical time. -/
theorem selected_generic_emit_preserving_a (i n k : Nat) (rows : EmitRows k)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (h : graphSystem.run i = cfgAS k base n 0 reserve) :
    ∃ finish : Snapshot,
      Good finish ∧
      finish.graphState = cfgAS (k+8) base n 0
        ((reserve ++ List.replicate n 0) ++ List.replicate n 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + (7*n+3))) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i + (7*n+3))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.unary n ∧
      graphRefinement.boundary i < graphRefinement.boundary (i + (7*n+3)) := by
  have block := generic_emit_preserving_a k rows n base reserve
  have hr : graphSystem.run (i + (7*n+3)) = cfgAS (k+8) base n 0
      ((reserve ++ List.replicate n 0) ++ List.replicate n 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i + (7*n+3)) =
      graphSystem.prefixWord i ++ PASoundness.UnaryCodec.unary n := by
    rw [WordEventSystem.prefix_add, h, block.output, unary_as_replicate]
  obtain ⟨finish, hg, hs, hc⟩ := graphRefinement.related (i + (7*n+3))
  refine ⟨finish, hg, hs.trans hr, hc, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

/-- The unpairing output bank and the emitter input bank coincide when the
emitter's scratch register is clear. -/
theorem unpair_exit_to_emit (k : Nat) (base : RegisterMachine.Bank 9)
    (rest a c : Nat) (reserve : List Nat) (hs : base 0 = 0) :
    cfgRAC k base rest a c reserve =
      cfgAS k (bankAC (bankRest base rest) a c) a 0 reserve := by
  unfold cfgRAC cfgAC cfgAS
  congr 1
  funext i
  fin_cases i <;> simp [bankAS, bankAC, bankRest, hs]

/-- A checked unpairing followed by the corresponding unary emitter computes
and emits the first Cantor component. This is a finite graph block from a
prepared entry, with arbitrary input and explicitly clear scratch. -/
theorem generic_unpair_then_emit (n k : Nat) (ur : UnpairRows k)
    (er : EmitRows (k+11)) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hs : base 0 = 0) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgRAC k base n 0 0 reserve)
        (duration + (7*(Cantor.unpair n).1+3))
        (cfgAS ((k+11)+8)
          (bankAC (bankRest base (Cantor.unpair n).2) (Cantor.unpair n).1 0)
          (Cantor.unpair n).1 0
          (((reserve ++ List.replicate padding 0) ++ List.replicate (Cantor.unpair n).1 0) ++
            List.replicate (Cantor.unpair n).1 0))
        (PASoundness.UnaryCodec.unary (Cantor.unpair n).1) := by
  obtain ⟨duration, padding, ht, hu⟩ := generic_unpair n k ur base reserve
  rw [unpair_exit_to_emit (k+11) base (Cantor.unpair n).2 (Cantor.unpair n).1 0 _ hs] at hu
  have he := generic_emit_preserving_a (k+11) er (Cantor.unpair n).1
    (bankAC (bankRest base (Cantor.unpair n).2) (Cantor.unpair n).1 0)
    (reserve ++ List.replicate padding 0)
  refine ⟨duration, padding, ht, ?_⟩
  simpa [unary_as_replicate] using hu.trans graphSystem he

end PASoundness.M236.OccurrenceGraph
