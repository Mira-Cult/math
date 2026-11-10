import PASoundness.M236GraphFullObserver
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def bankAC (base : RegisterMachine.Bank 9) (a c : Nat) : RegisterMachine.Bank 9 :=
  fun i => if i = 6 then a else if i = 8 then c else base i

def cfgAC (i : Nat) (base : RegisterMachine.Bank 9) (a c : Nat) (reserve : List Nat) : GraphState :=
  ⟨i, bankAC base a c, reserve⟩

theorem row11 : sourceRows[11]? = some ("3.k.c.decnz", 12, some 14) := by decide
theorem row12 : sourceRows[12]? = some ("3.k.a.inc", 13, none) := by decide
theorem row13 : sourceRows[13]? = some ("jump", 11, none) := by decide
theorem row14 : sourceRows[14]? = some ("jump", 7, none) := by decide

theorem dec_c (base : RegisterMachine.Bank 9) (a n : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAC 11 base a (n+1) reserve) = (cfgAC 12 base a n (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAC, row11, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, RegisterMachine.write])

theorem zero_c (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAC 11 base a 0 reserve) = (cfgAC 14 base a 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgAC, row11, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, RegisterMachine.execute, RegisterMachine.write]

theorem inc_a (base : RegisterMachine.Bank 9) (a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAC 12 base a c reserve) = (cfgAC 13 base (a+1) c reserve, []) := by
  simp [graphSystem, graphNext, cfgAC, row12, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, RegisterMachine.write])

theorem jump_to_c (base : RegisterMachine.Bank 9) (a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAC 13 base a c reserve) = (cfgAC 11 base a c reserve, []) := by
  simp [graphSystem, graphNext, cfgAC, row13, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, RegisterMachine.execute, RegisterMachine.write]

theorem jump_to_unpair (base : RegisterMachine.Bank 9) (a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAC 14 base a c reserve) = (cfgAC 7 base a c reserve, []) := by
  simp [graphSystem, graphNext, cfgAC, row14, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, RegisterMachine.execute, RegisterMachine.write]

theorem move_cycle (base : RegisterMachine.Bank 9) (a n : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAC 11 base a (n+1) reserve) 3
      (cfgAC 11 base (a+1) n (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (dec_c base a n reserve)
  have h2 := WordEventSystem.Block.single graphSystem (inc_a base a n (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (jump_to_c base (a+1) n (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem move_all (n : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAC 11 base a n reserve) (3*n)
      (cfgAC 11 base (a+n) 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing a reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgAC 11 base a 0 reserve)
  | succ n ih =>
    have h := (move_cycle base a n reserve).trans graphSystem (ih (a+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- The checked unpairing-control rows transfer all of c to a, clear c, and
return to the outer loop after exactly `3*n+2` silent graph steps. -/
theorem move_c_to_a (n : Nat) (base : RegisterMachine.Bank 9) (a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAC 11 base a n reserve) (3*n+2)
      (cfgAC 7 base (a+n) 0 (reserve ++ List.replicate n 0)) [] := by
  have h1 := move_all n base a reserve
  have h2 := WordEventSystem.Block.single graphSystem (zero_c base (a+n) (reserve ++ List.replicate n 0))
  have h3 := WordEventSystem.Block.single graphSystem (jump_to_unpair base (a+n) 0 (reserve ++ List.replicate n 0))
  simpa [Nat.add_assoc] using (h1.trans graphSystem h2).trans graphSystem h3

theorem move_at_graph_run (i n : Nat) (base : RegisterMachine.Bank 9) (a : Nat)
    (reserve : List Nat) (h : graphSystem.run i = cfgAC 11 base a n reserve) :
    graphSystem.run (i + (3*n+2)) = cfgAC 7 base (a+n) 0 (reserve ++ List.replicate n 0) ∧
    graphSystem.prefixWord (i + (3*n+2)) = graphSystem.prefixWord i := by
  have block := move_c_to_a n base a reserve
  constructor
  · rw [WordEventSystem.run_add, h, block.endpoint]
  · rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]

/-- Any reachable transfer entry on the selected blank-start execution has a
later full canonical boundary with the exact effect and no intervening event. -/
theorem selected_move_at_boundary (i n : Nat) (base : RegisterMachine.Bank 9) (a : Nat)
    (reserve : List Nat) (h : graphSystem.run i = cfgAC 11 base a n reserve) :
    ∃ finish : Snapshot,
      Good finish ∧
      finish.graphState = cfgAC 7 base (a+n) 0 (reserve ++ List.replicate n 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + (3*n+2))) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i + (3*n+2))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i + (3*n+2)) := by
  have ⟨hr, hp⟩ := move_at_graph_run i n base a reserve h
  obtain ⟨finish, hg, hs, hc⟩ := graphRefinement.related (i + (3*n+2))
  refine ⟨finish, hg, hs.trans hr, hc, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

end PASoundness.M236.OccurrenceGraph
