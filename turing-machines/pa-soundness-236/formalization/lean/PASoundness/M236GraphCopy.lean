import PASoundness.M236GraphFullObserver
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def bankWith (base : RegisterMachine.Bank 9) (stage rest scratch : Nat) : RegisterMachine.Bank 9 :=
  fun i => if i = 0 then scratch else if i = 1 then stage else if i = 2 then rest else base i

def cfg (i : Nat) (base : RegisterMachine.Bank 9) (stage rest scratch : Nat) (reserve : List Nat) : GraphState :=
  ⟨i, bankWith base stage rest scratch, reserve⟩

theorem row0 : sourceRows[0]? = some ("3.k.stage.decnz", 1, some 4) := by decide

theorem dec_stage (base : RegisterMachine.Bank 9) (n rest scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfg 0 base (n+1) rest scratch reserve) =
      (cfg 1 base n rest scratch (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfg, row0, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankWith, RegisterMachine.execute,
    RegisterMachine.write]
  funext i
  fin_cases i <;> simp [bankWith, RegisterMachine.write]

theorem row1 : sourceRows[1]? = some ("3.k.rest.inc", 2, none) := by decide
theorem row2 : sourceRows[2]? = some ("3.scratch.copy.inc", 3, none) := by decide
theorem row3 : sourceRows[3]? = some ("jump", 0, none) := by decide
theorem row4 : sourceRows[4]? = some ("3.scratch.copy.decnz", 5, some 7) := by decide
theorem row5 : sourceRows[5]? = some ("3.k.stage.inc", 6, none) := by decide
theorem row6 : sourceRows[6]? = some ("jump", 4, none) := by decide

theorem zero_stage (base : RegisterMachine.Bank 9) (rest scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfg 0 base 0 rest scratch reserve) = (cfg 4 base 0 rest scratch reserve, []) := by
  simp [graphSystem, graphNext, cfg, row0, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankWith, RegisterMachine.execute,
    RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankWith, RegisterMachine.write])

theorem inc_rest (base : RegisterMachine.Bank 9) (stage rest scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfg 1 base stage rest scratch reserve) = (cfg 2 base stage (rest+1) scratch reserve, []) := by
  simp [graphSystem, graphNext, cfg, row1, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankWith, RegisterMachine.execute,
    RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankWith, RegisterMachine.write])

theorem inc_scratch (base : RegisterMachine.Bank 9) (stage rest scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfg 2 base stage rest scratch reserve) = (cfg 3 base stage rest (scratch+1) reserve, []) := by
  simp [graphSystem, graphNext, cfg, row2, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankWith, RegisterMachine.execute,
    RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankWith, RegisterMachine.write])

theorem jump_to_stage (base : RegisterMachine.Bank 9) (stage rest scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfg 3 base stage rest scratch reserve) = (cfg 0 base stage rest scratch reserve, []) := by
  simp [graphSystem, graphNext, cfg, row3, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankWith, RegisterMachine.execute,
    RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankWith, RegisterMachine.write])

theorem dec_scratch (base : RegisterMachine.Bank 9) (stage rest n : Nat) (reserve : List Nat) :
    graphSystem.step (cfg 4 base stage rest (n+1) reserve) = (cfg 5 base stage rest n (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfg, row4, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankWith, RegisterMachine.execute,
    RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankWith, RegisterMachine.write])

theorem zero_scratch (base : RegisterMachine.Bank 9) (stage rest : Nat) (reserve : List Nat) :
    graphSystem.step (cfg 4 base stage rest 0 reserve) = (cfg 7 base stage rest 0 reserve, []) := by
  simp [graphSystem, graphNext, cfg, row4, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankWith, RegisterMachine.execute,
    RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankWith, RegisterMachine.write])

theorem inc_stage (base : RegisterMachine.Bank 9) (stage rest scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfg 5 base stage rest scratch reserve) = (cfg 6 base (stage+1) rest scratch reserve, []) := by
  simp [graphSystem, graphNext, cfg, row5, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankWith, RegisterMachine.execute,
    RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankWith, RegisterMachine.write])

theorem jump_to_scratch (base : RegisterMachine.Bank 9) (stage rest scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfg 6 base stage rest scratch reserve) = (cfg 4 base stage rest scratch reserve, []) := by
  simp [graphSystem, graphNext, cfg, row6, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankWith, RegisterMachine.execute,
    RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankWith, RegisterMachine.write])

/-- One nonzero transfer cycle: stage decreases, rest and scratch increase. -/
theorem transfer_cycle (base : RegisterMachine.Bank 9) (n rest scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfg 0 base (n+1) rest scratch reserve) 4
      (cfg 0 base n (rest+1) (scratch+1) (reserve ++ [0])) [] := by
  have a := WordEventSystem.Block.single graphSystem (dec_stage base n rest scratch reserve)
  have b := WordEventSystem.Block.single graphSystem (inc_rest base n rest scratch (reserve ++ [0]))
  have c := WordEventSystem.Block.single graphSystem (inc_scratch base n (rest+1) scratch (reserve ++ [0]))
  have d := WordEventSystem.Block.single graphSystem (jump_to_stage base n (rest+1) (scratch+1) (reserve ++ [0]))
  simpa using ((a.trans graphSystem b).trans graphSystem c).trans graphSystem d

/-- One nonzero restore cycle: scratch decreases and stage increases. -/
theorem restore_cycle (base : RegisterMachine.Bank 9) (stage rest n : Nat) (reserve : List Nat) :
    graphSystem.Block (cfg 4 base stage rest (n+1) reserve) 3
      (cfg 4 base (stage+1) rest n (reserve ++ [0])) [] := by
  have a := WordEventSystem.Block.single graphSystem (dec_scratch base stage rest n reserve)
  have b := WordEventSystem.Block.single graphSystem (inc_stage base stage rest n (reserve ++ [0]))
  have c := WordEventSystem.Block.single graphSystem (jump_to_scratch base (stage+1) rest n (reserve ++ [0]))
  simpa using (a.trans graphSystem b).trans graphSystem c

/-- The transfer phase terminates for every finite stage value. -/
theorem transfer_all (n : Nat) (base : RegisterMachine.Bank 9) (rest scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfg 0 base n rest scratch reserve) (4*n)
      (cfg 0 base 0 (rest+n) (scratch+n) (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing rest scratch reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfg 0 base 0 rest scratch reserve)
  | succ n ih =>
    have h := (transfer_cycle base n rest scratch reserve).trans graphSystem
      (ih (rest+1) (scratch+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- The restore phase terminates for every finite scratch value. -/
theorem restore_all (n : Nat) (base : RegisterMachine.Bank 9) (stage rest : Nat) (reserve : List Nat) :
    graphSystem.Block (cfg 4 base stage rest n reserve) (3*n)
      (cfg 4 base (stage+n) rest 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing stage reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfg 4 base stage rest 0 reserve)
  | succ n ih =>
    have h := (restore_cycle base stage rest n reserve).trans graphSystem
      (ih (stage+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- Rows 0–6 copy stage into rest, restore stage, and clear an initially
zero scratch register in exactly `7*n + 2` silent graph steps. -/
theorem copy_stage (n : Nat) (base : RegisterMachine.Bank 9) (rest : Nat) (reserve : List Nat) :
    graphSystem.Block (cfg 0 base n rest 0 reserve) (7*n+2)
      (cfg 7 base n (rest+n) 0 ((reserve ++ List.replicate n 0) ++ List.replicate n 0)) [] := by
  have a : graphSystem.Block (cfg 0 base n rest 0 reserve) (4*n)
      (cfg 0 base 0 (rest+n) n (reserve ++ List.replicate n 0)) [] := by
    simpa only [Nat.zero_add] using transfer_all n base rest 0 reserve
  have b := WordEventSystem.Block.single graphSystem
    (zero_stage base (rest+n) n (reserve ++ List.replicate n 0))
  have c : graphSystem.Block (cfg 4 base 0 (rest+n) n (reserve ++ List.replicate n 0)) (3*n)
      (cfg 4 base n (rest+n) 0 ((reserve ++ List.replicate n 0) ++ List.replicate n 0)) [] := by
    simpa only [Nat.zero_add] using restore_all n base 0 (rest+n) (reserve ++ List.replicate n 0)
  have d := WordEventSystem.Block.single graphSystem
    (zero_scratch base n (rest+n) ((reserve ++ List.replicate n 0) ++ List.replicate n 0))
  have h := ((a.trans graphSystem b).trans graphSystem c).trans graphSystem d
  have ht : 4*n+1+3*n+1 = 7*n+2 := by omega
  simpa [ht] using h

/-- On a reachable graph run, the copy has its exact silent prefix effect. -/
theorem copy_at_graph_run (i n : Nat) (base : RegisterMachine.Bank 9) (rest : Nat)
    (reserve : List Nat) (h : graphSystem.run i = cfg 0 base n rest 0 reserve) :
    graphSystem.run (i + (7*n+2)) =
      cfg 7 base n (rest+n) 0 ((reserve ++ List.replicate n 0) ++ List.replicate n 0) ∧
    graphSystem.prefixWord (i + (7*n+2)) = graphSystem.prefixWord i := by
  have block := copy_stage n base rest reserve
  constructor
  · rw [WordEventSystem.run_add, h, block.endpoint]
  · rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]

/-- At any reachable copy entry, the selected physical run reaches the
corresponding complete-tape boundary later, with no intervening event. -/
theorem selected_copy_at_boundary (i n : Nat) (base : RegisterMachine.Bank 9) (rest : Nat)
    (reserve : List Nat) (h : graphSystem.run i = cfg 0 base n rest 0 reserve) :
    ∃ finish : Snapshot,
      Good finish ∧
      finish.graphState = cfg 7 base n (rest+n) 0
        ((reserve ++ List.replicate n 0) ++ List.replicate n 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + (7*n+2))) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i + (7*n+2))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i + (7*n+2)) := by
  have ⟨hr, hp⟩ := copy_at_graph_run i n base rest reserve h
  obtain ⟨finish, hg, hs, hc⟩ := graphRefinement.related (i + (7*n+2))
  refine ⟨finish, hg, hs.trans hr, hc, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

/-- The completely blank execution's certified graph entry satisfies the
copy precondition with all three registers zero. -/
theorem initial_copy_entry : graphSystem.run 0 = cfg 0 BlankFirst.zeros 0 0 0 BlankFirst.reserve := by
  change graphInitial = cfg 0 BlankFirst.zeros 0 0 0 BlankFirst.reserve
  unfold graphInitial cfg
  congr 1
  funext i
  simp [bankWith, BlankFirst.zeros]

/-- The initial zero-valued copy is reached on the actual selected blank run. -/
theorem initial_copy_on_selected :
    ∃ finish : Snapshot,
      Good finish ∧ finish.graphState = cfg 7 BlankFirst.zeros 0 0 0 BlankFirst.reserve ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary 2) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary 2) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary 0) ∧
      graphRefinement.boundary 0 < graphRefinement.boundary 2 := by
  simpa using selected_copy_at_boundary 0 0 BlankFirst.zeros 0 BlankFirst.reserve initial_copy_entry

end PASoundness.M236.OccurrenceGraph
