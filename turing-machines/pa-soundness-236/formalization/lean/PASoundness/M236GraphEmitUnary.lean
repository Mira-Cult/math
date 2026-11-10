import PASoundness.M236GraphFullObserver
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def bankAS (base : RegisterMachine.Bank 9) (a scratch : Nat) : RegisterMachine.Bank 9 :=
  fun i => if i = 0 then scratch else if i = 6 then a else base i

def cfgAS (i : Nat) (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) : GraphState :=
  ⟨i, bankAS base a scratch, reserve⟩

theorem row19 : sourceRows[19]? = some ("3.k.a.decnz", 20, some 23) := by decide
theorem row20 : sourceRows[20]? = some ("emit.1", 21, none) := by decide
theorem row21 : sourceRows[21]? = some ("3.scratch.copy.inc", 22, none) := by decide
theorem row22 : sourceRows[22]? = some ("jump", 19, none) := by decide
theorem row23 : sourceRows[23]? = some ("emit.0", 24, none) := by decide
theorem row24 : sourceRows[24]? = some ("3.scratch.copy.decnz", 25, some 27) := by decide
theorem row25 : sourceRows[25]? = some ("3.k.a.inc", 26, none) := by decide
theorem row26 : sourceRows[26]? = some ("jump", 24, none) := by decide

theorem dec_a19 (base : RegisterMachine.Bank 9) (n scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 19 base (n+1) scratch reserve) = (cfgAS 20 base n scratch (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAS, row19, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAS, RegisterMachine.write])

theorem zero_a19 (base : RegisterMachine.Bank 9) (scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 19 base 0 scratch reserve) = (cfgAS 23 base 0 scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, row19, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute, RegisterMachine.write]

theorem emit_one20 (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 20 base a scratch reserve) = (cfgAS 21 base a scratch reserve, [true]) := by
  simp [graphSystem, graphNext, cfgAS, row20, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem inc_scratch21 (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 21 base a scratch reserve) = (cfgAS 22 base a (scratch+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, row21, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAS, RegisterMachine.write])

theorem jump22 (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 22 base a scratch reserve) = (cfgAS 19 base a scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, row22, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem emit_zero23 (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 23 base a scratch reserve) = (cfgAS 24 base a scratch reserve, [false]) := by
  simp [graphSystem, graphNext, cfgAS, row23, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem dec_scratch24 (base : RegisterMachine.Bank 9) (a n : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 24 base a (n+1) reserve) = (cfgAS 25 base a n (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAS, row24, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAS, RegisterMachine.write])

theorem zero_scratch24 (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 24 base a 0 reserve) = (cfgAS 27 base a 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, row24, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute, RegisterMachine.write]

theorem inc_a25 (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 25 base a scratch reserve) = (cfgAS 26 base (a+1) scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, row25, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAS, RegisterMachine.write])

theorem jump26 (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 26 base a scratch reserve) = (cfgAS 24 base a scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, row26, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem emit_cycle (base : RegisterMachine.Bank 9) (n scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAS 19 base (n+1) scratch reserve) 4
      (cfgAS 19 base n (scratch+1) (reserve ++ [0])) [true] := by
  have h1 := WordEventSystem.Block.single graphSystem (dec_a19 base n scratch reserve)
  have h2 := WordEventSystem.Block.single graphSystem (emit_one20 base n scratch (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (inc_scratch21 base n scratch (reserve ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (jump22 base n (scratch+1) (reserve ++ [0]))
  simpa using ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4

theorem emit_many (n : Nat) (base : RegisterMachine.Bank 9) (scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAS 19 base n scratch reserve) (4*n)
      (cfgAS 19 base 0 (scratch+n) (reserve ++ List.replicate n 0)) (List.replicate n true) := by
  induction n generalizing scratch reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgAS 19 base 0 scratch reserve)
  | succ n ih =>
    have h := (emit_cycle base n scratch reserve).trans graphSystem (ih (scratch+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem restore_a_cycle (base : RegisterMachine.Bank 9) (a n : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAS 24 base a (n+1) reserve) 3
      (cfgAS 24 base (a+1) n (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (dec_scratch24 base a n reserve)
  have h2 := WordEventSystem.Block.single graphSystem (inc_a25 base a n (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (jump26 base (a+1) n (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem restore_a_all (n : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAS 24 base a n reserve) (3*n)
      (cfgAS 24 base (a+n) 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing a reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgAS 24 base a 0 reserve)
  | succ n ih =>
    have h := (restore_a_cycle base a n reserve).trans graphSystem (ih (a+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- Emit the natural in unary, restore a and clear initially zero scratch. -/
theorem emit_preserving_a (n : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    graphSystem.Block (cfgAS 19 base n 0 reserve) (7*n+3)
      (cfgAS 27 base n 0 ((reserve ++ List.replicate n 0) ++ List.replicate n 0))
      (List.replicate n true ++ [false]) := by
  have h1 : graphSystem.Block (cfgAS 19 base n 0 reserve) (4*n)
      (cfgAS 19 base 0 n (reserve ++ List.replicate n 0)) (List.replicate n true) := by
    simpa only [Nat.zero_add] using emit_many n base 0 reserve
  have h2 := WordEventSystem.Block.single graphSystem (zero_a19 base n (reserve ++ List.replicate n 0))
  have h3 := WordEventSystem.Block.single graphSystem (emit_zero23 base 0 n (reserve ++ List.replicate n 0))
  have h4 : graphSystem.Block (cfgAS 24 base 0 n (reserve ++ List.replicate n 0)) (3*n)
      (cfgAS 24 base n 0 ((reserve ++ List.replicate n 0) ++ List.replicate n 0)) [] := by
    simpa only [Nat.zero_add] using restore_a_all n base 0 (reserve ++ List.replicate n 0)
  have h5 := WordEventSystem.Block.single graphSystem
    (zero_scratch24 base n ((reserve ++ List.replicate n 0) ++ List.replicate n 0))
  have h := (((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5
  have ht : 4*n+1+1+3*n+1 = 7*n+3 := by omega
  simpa [ht] using h
theorem unary_as_replicate (n : Nat) : PASoundness.UnaryCodec.unary n =
    List.replicate n true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [PASoundness.UnaryCodec.unary, List.replicate_succ, ih]

/-- At a reachable rank-output entry, the selected machine emits the exact
unary field and reaches the restored canonical boundary in positive time. -/
theorem selected_emit_preserving_a (i n : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (h : graphSystem.run i = cfgAS 19 base n 0 reserve) :
    ∃ finish : Snapshot,
      Good finish ∧
      finish.graphState = cfgAS 27 base n 0
        ((reserve ++ List.replicate n 0) ++ List.replicate n 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + (7*n+3))) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i + (7*n+3))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.unary n ∧
      graphRefinement.boundary i < graphRefinement.boundary (i + (7*n+3)) := by
  have block := emit_preserving_a n base reserve
  have hr : graphSystem.run (i + (7*n+3)) = cfgAS 27 base n 0
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

end PASoundness.M236.OccurrenceGraph
