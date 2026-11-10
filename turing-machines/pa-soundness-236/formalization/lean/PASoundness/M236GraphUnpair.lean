import PASoundness.M236GraphMove
import PASoundness.M236GraphCopy
import PASoundness.M236UnpairDiagonal
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def bankRest (base : RegisterMachine.Bank 9) (rest : Nat) : RegisterMachine.Bank 9 :=
  fun i => if i = 2 then rest else base i

def cfgRAC (i : Nat) (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) : GraphState :=
  cfgAC i (bankRest base rest) a c reserve

theorem row7 : sourceRows[7]? = some ("3.k.rest.decnz", 8, some 15) := by decide
theorem row8 : sourceRows[8]? = some ("3.k.c.inc", 9, none) := by decide
theorem row9 : sourceRows[9]? = some ("3.k.a.decnz", 10, some 11) := by decide
theorem row10 : sourceRows[10]? = some ("jump", 14, none) := by decide

theorem dec_rest (base : RegisterMachine.Bank 9) (n a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC 7 base (n+1) a c reserve) = (cfgRAC 8 base n a c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, row7, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, bankRest, RegisterMachine.write])

theorem zero_rest (base : RegisterMachine.Bank 9) (a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC 7 base 0 a c reserve) = (cfgRAC 15 base 0 a c reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, row7, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]

theorem inc_c (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC 8 base rest a c reserve) = (cfgRAC 9 base rest a (c+1) reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, row8, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, bankRest, RegisterMachine.write])

theorem dec_a (base : RegisterMachine.Bank 9) (rest n c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC 9 base rest (n+1) c reserve) =
      (cfgRAC 10 base rest n c (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, row9, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, bankRest, RegisterMachine.write])

theorem zero_a (base : RegisterMachine.Bank 9) (rest c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC 9 base rest 0 c reserve) = (cfgRAC 11 base rest 0 c reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, row9, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]

theorem jump10 (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC 10 base rest a c reserve) = (cfgRAC 14 base rest a c reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, row10, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]

theorem jump14 (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC 14 base rest a c reserve) = (cfgRAC 7 base rest a c reserve, []) := by
  exact jump_to_unpair (bankRest base rest) a c reserve

/-- One outer iteration when the a counter is positive. -/
theorem diagonal_positive (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgRAC 7 base (rest+1) (a+1) c reserve) 5
      (cfgRAC 7 base rest a (c+1) ((reserve ++ [0]) ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (dec_rest base rest (a+1) c reserve)
  have h2 := WordEventSystem.Block.single graphSystem (inc_c base rest (a+1) c (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (dec_a base rest a (c+1) (reserve ++ [0]))
  have h4 := WordEventSystem.Block.single graphSystem (jump10 base rest a (c+1) ((reserve ++ [0]) ++ [0]))
  have h5 := WordEventSystem.Block.single graphSystem (jump14 base rest a (c+1) ((reserve ++ [0]) ++ [0]))
  simpa using ((((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4).trans graphSystem h5)

/-- One outer iteration at the diagonal boundary transfers c+1 into a. -/
theorem diagonal_zero (base : RegisterMachine.Bank 9) (rest c : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgRAC 7 base (rest+1) 0 c reserve) (3*(c+1)+5)
      (cfgRAC 7 base rest (c+1) 0 ((reserve ++ [0]) ++ List.replicate (c+1) 0)) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (dec_rest base rest 0 c reserve)
  have h2 := WordEventSystem.Block.single graphSystem (inc_c base rest 0 c (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (zero_a base rest (c+1) (reserve ++ [0]))
  have h4 := move_c_to_a (c+1) (bankRest base rest) 0 (reserve ++ [0])
  have h := ((h1.trans graphSystem h2).trans graphSystem h3).trans graphSystem h4
  have ht : 3 + (3*(c+1)+2) = 3*(c+1)+5 := by omega
  simpa only [cfgRAC, Nat.zero_add, List.nil_append, Nat.reduceAdd, ht] using h
/-- The whole diagonal scan terminates for any remaining input and starts
from arbitrary diagonal coordinates. Its reserve only gains zero blocks. -/
theorem diagonal_phase (remaining : Nat) (base : RegisterMachine.Bank 9)
    (a c : Nat) (reserve : List Nat) :
    ∃ duration padding, remaining+1 ≤ duration ∧
      graphSystem.Block (cfgRAC 7 base remaining a c reserve) duration
        (cfgRAC 15 base 0 (M236.UnpairDiagonal.walk remaining (a,c)).1
          (M236.UnpairDiagonal.walk remaining (a,c)).2
          (reserve ++ List.replicate padding 0)) [] := by
  induction remaining generalizing a c reserve with
  | zero =>
    refine ⟨1, 0, by omega, ?_⟩
    simpa [M236.UnpairDiagonal.walk] using WordEventSystem.Block.single graphSystem (zero_rest base a c reserve)
  | succ n ih =>
    cases a with
    | zero =>
      obtain ⟨duration, padding, ht, htail⟩ := ih (c+1) 0 ((reserve ++ [0]) ++ List.replicate (c+1) 0)
      have h := (diagonal_zero base n c reserve).trans graphSystem htail
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
      have h := (diagonal_positive base n a c reserve).trans graphSystem htail
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
theorem diagonal_unpair (n : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgRAC 7 base n 0 0 reserve) duration
        (cfgRAC 15 base 0 (Cantor.unpair n).1 (Cantor.unpair n).2
          (reserve ++ List.replicate padding 0)) [] := by
  simpa only [M236.UnpairDiagonal.walk_zero] using diagonal_phase n base 0 0 reserve

/-- At any reachable diagonal-scan entry, the selected machine reaches a
later canonical boundary containing the exact Cantor inverse, silently. -/
theorem selected_diagonal_unpair (i n : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (h : graphSystem.run i = cfgRAC 7 base n 0 0 reserve) :
    ∃ duration padding finish,
      n+1 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgRAC 15 base 0 (Cantor.unpair n).1 (Cantor.unpair n).2
        (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i + duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i + duration) := by
  obtain ⟨duration, padding, ht, block⟩ := diagonal_unpair n base reserve
  have hr : graphSystem.run (i+duration) =
      cfgRAC 15 base 0 (Cantor.unpair n).1 (Cantor.unpair n).2
        (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hs, hc⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hs.trans hr, hc, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

/-- The initial silent copy reaches the zero-input diagonal entry. -/
theorem initial_diagonal_entry : graphSystem.run 2 =
    cfgRAC 7 BlankFirst.zeros 0 0 0 BlankFirst.reserve := by
  have hp := (copy_at_graph_run 0 0 BlankFirst.zeros 0 BlankFirst.reserve initial_copy_entry).1
  have hc : cfg 7 BlankFirst.zeros 0 0 0 BlankFirst.reserve =
      cfgRAC 7 BlankFirst.zeros 0 0 0 BlankFirst.reserve := by
    unfold cfg cfgRAC cfgAC
    congr 1
    funext i
    simp [bankWith, bankAC, bankRest, BlankFirst.zeros]
  have hp' : graphSystem.run 2 = cfg 7 BlankFirst.zeros 0 0 0 BlankFirst.reserve := by simpa using hp
  exact hp'.trans hc

/-- The selected blank-start run enters and completes the zero-input scan. -/
theorem initial_diagonal_on_selected :
    ∃ duration padding finish,
      1 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgRAC 15 BlankFirst.zeros 0 0 0
        (BlankFirst.reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (2 + duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (2 + duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary 2) ∧
      graphRefinement.boundary 2 < graphRefinement.boundary (2 + duration) := by
  simpa [Cantor.unpair, Cantor.unpairAux] using
    selected_diagonal_unpair 2 0 BlankFirst.zeros BlankFirst.reserve initial_diagonal_entry

theorem row15 : sourceRows[15]? = some ("3.k.c.decnz", 16, some 18) := by decide
theorem row16 : sourceRows[16]? = some ("3.k.rest.inc", 17, none) := by decide
theorem row17 : sourceRows[17]? = some ("jump", 15, none) := by decide
theorem row18 : sourceRows[18]? = some ("3.k.a.inc", 19, none) := by decide

theorem dec_c15 (base : RegisterMachine.Bank 9) (rest a n : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC 15 base rest a (n+1) reserve) =
      (cfgRAC 16 base rest a n (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, row15, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, bankRest, RegisterMachine.write])

theorem zero_c15 (base : RegisterMachine.Bank 9) (rest a : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC 15 base rest a 0 reserve) = (cfgRAC 18 base rest a 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, row15, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]

theorem inc_rest16 (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC 16 base rest a c reserve) = (cfgRAC 17 base (rest+1) a c reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, row16, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, bankRest, RegisterMachine.write])

theorem jump17 (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC 17 base rest a c reserve) = (cfgRAC 15 base rest a c reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, row17, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]

theorem inc_a18 (base : RegisterMachine.Bank 9) (rest a c : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC 18 base rest a c reserve) = (cfgRAC 19 base rest (a+1) c reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, row18, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, bankRest, RegisterMachine.write])

theorem drain_cycle (base : RegisterMachine.Bank 9) (rest a n : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgRAC 15 base rest a (n+1) reserve) 3
      (cfgRAC 15 base (rest+1) a n (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (dec_c15 base rest a n reserve)
  have h2 := WordEventSystem.Block.single graphSystem (inc_rest16 base rest a n (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (jump17 base (rest+1) a n (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem drain_all (n : Nat) (base : RegisterMachine.Bank 9) (rest a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgRAC 15 base rest a n reserve) (3*n)
      (cfgRAC 15 base (rest+n) a 0 (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing rest reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgRAC 15 base rest a 0 reserve)
  | succ n ih =>
    have h := (drain_cycle base rest a n reserve).trans graphSystem (ih (rest+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- Move the second Cantor component into rest, then increment a for the
subsequent rank field. -/
theorem unpair_finish (n : Nat) (base : RegisterMachine.Bank 9) (rest a : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgRAC 15 base rest a n reserve) (3*n+2)
      (cfgRAC 19 base (rest+n) (a+1) 0 (reserve ++ List.replicate n 0)) [] := by
  have h1 := drain_all n base rest a reserve
  have h2 := WordEventSystem.Block.single graphSystem (zero_c15 base (rest+n) a (reserve ++ List.replicate n 0))
  have h3 := WordEventSystem.Block.single graphSystem (inc_a18 base (rest+n) a 0 (reserve ++ List.replicate n 0))
  simpa [Nat.add_assoc] using (h1.trans graphSystem h2).trans graphSystem h3

/-- Rows 7–18 compute the exact Cantor inverse, leave its second component in
rest and its first component plus one in a, and terminate silently. -/
theorem unpair_to_rank_entry (n : Nat) (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgRAC 7 base n 0 0 reserve) duration
        (cfgRAC 19 base (Cantor.unpair n).2 ((Cantor.unpair n).1+1) 0
          (reserve ++ List.replicate padding 0)) [] := by
  obtain ⟨duration, padding, ht, hscan⟩ := diagonal_unpair n base reserve
  have hfinish := unpair_finish (Cantor.unpair n).2 base 0 (Cantor.unpair n).1
    (reserve ++ List.replicate padding 0)
  have h := hscan.trans graphSystem hfinish
  refine ⟨duration + (3*(Cantor.unpair n).2+2), padding+(Cantor.unpair n).2, by omega, ?_⟩
  have hres : (reserve ++ List.replicate padding 0) ++ List.replicate (Cantor.unpair n).2 0 =
      reserve ++ List.replicate (padding+(Cantor.unpair n).2) 0 := by
    conv_rhs => rw [List.replicate_add]
    simp only [List.append_assoc]
  rw [← hres]
  simpa only [Nat.zero_add, List.nil_append] using h

/-- Lift the full rows 7–18 contract to any reachable entry of the selected
literal blank-start execution, retaining its complete canonical tape state. -/
theorem selected_unpair_to_rank_entry (i n : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (h : graphSystem.run i = cfgRAC 7 base n 0 0 reserve) :
    ∃ duration padding finish,
      n+1 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgRAC 19 base (Cantor.unpair n).2 ((Cantor.unpair n).1+1) 0
        (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i + duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i + duration) := by
  obtain ⟨duration, padding, ht, block⟩ := unpair_to_rank_entry n base reserve
  have hr : graphSystem.run (i+duration) =
      cfgRAC 19 base (Cantor.unpair n).2 ((Cantor.unpair n).1+1) 0
        (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i := by
    rw [WordEventSystem.prefix_add, h, block.output, List.append_nil]
  obtain ⟨finish, hg, hs, hc⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hs.trans hr, hc, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

/-- The blank-start run reaches and completes its initial zero-input unpairing
phase, arriving at the first rank-output control entry. -/
theorem initial_unpair_to_rank_entry :
    ∃ duration padding finish,
      1 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgRAC 19 BlankFirst.zeros 0 1 0
        (BlankFirst.reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (2 + duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (2 + duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary 2) ∧
      graphRefinement.boundary 2 < graphRefinement.boundary (2 + duration) := by
  simpa [Cantor.unpair, Cantor.unpairAux] using
    selected_unpair_to_rank_entry 2 0 BlankFirst.zeros BlankFirst.reserve initial_diagonal_entry

end PASoundness.M236.OccurrenceGraph
