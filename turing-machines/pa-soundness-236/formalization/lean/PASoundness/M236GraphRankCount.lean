import PASoundness.M236RankHeader
/-! Transfer the rank into the scheduler's coordinate counter. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def bankCountA (base : RegisterMachine.Bank 9) (count a : Nat) : RegisterMachine.Bank 9 :=
  fun i => if i = 3 then count else if i = 6 then a else base i

def cfgCountA (i : Nat) (base : RegisterMachine.Bank 9) (count a : Nat)
    (reserve : List Nat) : GraphState := ⟨i, bankCountA base count a, reserve⟩

theorem row27 : sourceRows[27]? = some ("3.k.a.decnz", 28, some 30) := by decide
theorem row28 : sourceRows[28]? = some ("3.k.count.inc", 29, none) := by decide
theorem row29 : sourceRows[29]? = some ("jump", 27, none) := by decide

theorem rank_dec_a (base : RegisterMachine.Bank 9) (count n : Nat) (reserve : List Nat) :
    graphSystem.step (cfgCountA 27 base count (n+1) reserve) =
      (cfgCountA 28 base count n (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgCountA, row27, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankCountA, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankCountA, RegisterMachine.write])

theorem rank_zero_a (base : RegisterMachine.Bank 9) (count : Nat) (reserve : List Nat) :
    graphSystem.step (cfgCountA 27 base count 0 reserve) = (cfgCountA 30 base count 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgCountA, row27, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankCountA, RegisterMachine.execute, RegisterMachine.write]

theorem rank_inc_count (base : RegisterMachine.Bank 9) (count a : Nat) (reserve : List Nat) :
    graphSystem.step (cfgCountA 28 base count a reserve) = (cfgCountA 29 base (count+1) a reserve, []) := by
  simp [graphSystem, graphNext, cfgCountA, row28, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankCountA, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankCountA, RegisterMachine.write])

theorem rank_jump (base : RegisterMachine.Bank 9) (count a : Nat) (reserve : List Nat) :
    graphSystem.step (cfgCountA 29 base count a reserve) = (cfgCountA 27 base count a reserve, []) := by
  simp [graphSystem, graphNext, cfgCountA, row29, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankCountA, RegisterMachine.execute, RegisterMachine.write]

theorem rank_count_cycle (base : RegisterMachine.Bank 9) (count n : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgCountA 27 base count (n+1) reserve) 3
      (cfgCountA 27 base (count+1) n (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (rank_dec_a base count n reserve)
  have h2 := WordEventSystem.Block.single graphSystem (rank_inc_count base count n (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (rank_jump base (count+1) n (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem rank_count_all (n : Nat) (base : RegisterMachine.Bank 9) (count : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgCountA 27 base count n reserve) (3*n)
      (cfgCountA 27 base (count+n) 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing count reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgCountA 27 base count 0 reserve)
  | succ n ih =>
    have h := (rank_count_cycle base count n reserve).trans graphSystem (ih (count+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- Transfer any finite rank into the counter, with exact silent duration. -/
theorem rank_to_count (n : Nat) (base : RegisterMachine.Bank 9) (count : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgCountA 27 base count n reserve) (3*n+1)
      (cfgCountA 30 base (count+n) 0 (reserve ++ List.replicate n 0)) [] := by
  have h1 := rank_count_all n base count reserve
  have h2 := WordEventSystem.Block.single graphSystem (rank_zero_a base (count+n) (reserve ++ List.replicate n 0))
  simpa using h1.trans graphSystem h2


/-- The emission routine's restored rank can enter the transfer without
changing any register, including its restored scratch. -/
theorem rank_count_entry (base : RegisterMachine.Bank 9) (rank : Nat) (reserve : List Nat) :
    cfgAS 27 base rank 0 reserve = cfgCountA 27 (bankAS base rank 0) (base 3) rank reserve := by
  unfold cfgAS cfgCountA
  congr 1
  funext i
  fin_cases i <;> simp [bankCountA, bankAS]

/-- Transfer at a reachable graph boundary on the selected blank-start run. -/
theorem selected_rank_to_count (i n : Nat) (base : RegisterMachine.Bank 9) (count : Nat)
    (reserve : List Nat) (h : graphSystem.run i = cfgCountA 27 base count n reserve) :
    ∃ finish : Snapshot,
      Good finish ∧
      finish.graphState = cfgCountA 30 base (count+n) 0 (reserve ++ List.replicate n 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + (3*n+1))) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i + (3*n+1))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i + (3*n+1)) := by
  have block := rank_to_count n base count reserve
  have hr : graphSystem.run (i + (3*n+1)) =
      cfgCountA 30 base (count+n) 0 (reserve ++ List.replicate n 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i + (3*n+1)) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hs, hc⟩ := graphRefinement.related (i + (3*n+1))
  refine ⟨finish, hg, hs.trans hr, hc, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega


/-- Emission followed by rank transfer, preserving the exact unary word. -/
theorem emit_then_rank_to_count (n : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    graphSystem.Block (cfgAS 19 base n 0 reserve) ((7*n+3) + (3*n+1))
      (cfgCountA 30 (bankAS base n 0) (base 3+n) 0
        (((reserve ++ List.replicate n 0) ++ List.replicate n 0) ++ List.replicate n 0))
      (PASoundness.UnaryCodec.unary n) := by
  have hem := emit_preserving_a n base reserve
  rw [rank_count_entry base n ((reserve ++ List.replicate n 0) ++ List.replicate n 0)] at hem
  have ht := rank_to_count n (bankAS base n 0) (base 3)
    ((reserve ++ List.replicate n 0) ++ List.replicate n 0)
  simpa only [List.append_nil, unary_as_replicate] using hem.trans graphSystem ht

end PASoundness.M236.OccurrenceGraph
