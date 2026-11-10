import PASoundness.M236CoordinateOverflow

/-! The finite residual-coordinate output loop in the checked graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

theorem residual_unpair_rows : UnpairRows 727 := by constructor <;> decide
theorem residual_emit_rows : EmitRows 738 := by constructor <;> decide
theorem residual_row746 : sourceRows[746]? = some ("3.k.a.decnz", 747, some 748) := by decide
theorem residual_row747 : sourceRows[747]? = some ("jump", 746, none) := by decide
theorem residual_row748 : sourceRows[748]? = some ("jump", 726, none) := by decide

theorem residual_clear_dec (base : RegisterMachine.Bank 9) (n scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 746 base (n+1) scratch reserve) =
      (cfgAS 747 base n scratch (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgAS, residual_row746, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAS, RegisterMachine.write])

theorem residual_clear_zero (base : RegisterMachine.Bank 9) (scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 746 base 0 scratch reserve) = (cfgAS 748 base 0 scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, residual_row746, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAS, RegisterMachine.execute, RegisterMachine.write]

theorem residual_clear_jump (base : RegisterMachine.Bank 9) (a scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 747 base a scratch reserve) = (cfgAS 746 base a scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, residual_row747, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem residual_return_jump (base : RegisterMachine.Bank 9) (scratch : Nat) (reserve : List Nat) :
    graphSystem.step (cfgAS 748 base 0 scratch reserve) = (cfgAS 726 base 0 scratch reserve, []) := by
  simp [graphSystem, graphNext, cfgAS, residual_row748, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem residual_clear_all (n : Nat) (base : RegisterMachine.Bank 9) (scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAS 746 base n scratch reserve) (2*n)
      (cfgAS 746 base 0 scratch (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgAS 746 base 0 scratch reserve)
  | succ n ih =>
    have h1 := WordEventSystem.Block.single graphSystem (residual_clear_dec base n scratch reserve)
    have h2 := WordEventSystem.Block.single graphSystem (residual_clear_jump base n scratch (reserve ++ [0]))
    have h := (h1.trans graphSystem h2).trans graphSystem (ih (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

theorem residual_clear_return (n : Nat) (base : RegisterMachine.Bank 9) (scratch : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgAS 746 base n scratch reserve) (2*n+2)
      (cfgAS 726 base 0 scratch (reserve ++ List.replicate n 0)) [] := by
  have h1 := residual_clear_all n base scratch reserve
  have h2 := WordEventSystem.Block.single graphSystem (residual_clear_zero base scratch (reserve ++ List.replicate n 0))
  have h3 := WordEventSystem.Block.single graphSystem (residual_return_jump base scratch (reserve ++ List.replicate n 0))
  simpa [Nat.add_assoc] using (h1.trans graphSystem h2).trans graphSystem h3

theorem residual_count_positive (base : RegisterMachine.Bank 9) (count rest : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC 726 (bankOnlyCount base (count+1)) rest 0 0 reserve) =
      (cfgRAC 727 (bankOnlyCount base count) rest 0 0 (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, cleanup_row726, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, bankOnlyCount,
    RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> simp [bankAC, bankRest, bankOnlyCount, RegisterMachine.write])

theorem residual_count_zero (base : RegisterMachine.Bank 9) (rest : Nat) (reserve : List Nat) :
    graphSystem.step (cfgRAC 726 (bankOnlyCount base 0) rest 0 0 reserve) =
      (cfgRAC 749 (bankOnlyCount base 0) rest 0 0 reserve, []) := by
  simp [graphSystem, graphNext, cfgRAC, cfgAC, cleanup_row726, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankAC, bankRest, bankOnlyCount,
    RegisterMachine.execute, RegisterMachine.write]

theorem residual_emit_return_bank (base : RegisterMachine.Bank 9) (count rest a : Nat)
    (reserve : List Nat) (hs : base 0 = 0) :
    cfgAS 726 (bankAC (bankRest (bankOnlyCount base count) rest) a 0) 0 0 reserve =
      cfgRAC 726 (bankOnlyCount base count) rest 0 0 reserve := by
  unfold cfgAS cfgRAC cfgAC
  congr 1
  funext i
  fin_cases i <;> simp [bankAS, bankAC, bankRest, bankOnlyCount, hs]

/-- One positive-count iteration decodes and emits one unary coordinate, then
returns with its counter decremented and its work registers clear. -/
theorem residual_coordinate_one (base : RegisterMachine.Bank 9) (count rest : Nat)
    (reserve : List Nat) (hs : base 0 = 0) :
    ∃ duration padding, rest+1 ≤ duration ∧
      graphSystem.Block (cfgRAC 726 (bankOnlyCount base (count+1)) rest 0 0 reserve) duration
        (cfgRAC 726 (bankOnlyCount base count) (Cantor.unpair rest).2 0 0
          (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.unary (Cantor.unpair rest).1) := by
  have h1 := WordEventSystem.Block.single graphSystem (residual_count_positive base count rest reserve)
  obtain ⟨duration, padding, hd, hscan⟩ :=
    generic_unpair rest 727 residual_unpair_rows (bankOnlyCount base count) (reserve ++ [0])
  have hs' : bankOnlyCount base count 0 = 0 := by simp [bankOnlyCount, hs]
  rw [unpair_exit_to_emit 738 (bankOnlyCount base count) (Cantor.unpair rest).2
    (Cantor.unpair rest).1 0 _ hs'] at hscan
  have hem := generic_emit_preserving_a 738 residual_emit_rows (Cantor.unpair rest).1
    (bankAC (bankRest (bankOnlyCount base count) (Cantor.unpair rest).2) (Cantor.unpair rest).1 0)
    ((reserve ++ [0]) ++ List.replicate padding 0)
  have hclear := residual_clear_return (Cantor.unpair rest).1
    (bankAC (bankRest (bankOnlyCount base count) (Cantor.unpair rest).2) (Cantor.unpair rest).1 0) 0
    ((((reserve ++ [0]) ++ List.replicate padding 0) ++ List.replicate (Cantor.unpair rest).1 0) ++
      List.replicate (Cantor.unpair rest).1 0)
  rw [residual_emit_return_bank base count (Cantor.unpair rest).2 (Cantor.unpair rest).1 _ hs] at hclear
  have hres : (((((reserve ++ [0]) ++ List.replicate padding 0) ++ List.replicate (Cantor.unpair rest).1 0) ++
      List.replicate (Cantor.unpair rest).1 0) ++ List.replicate (Cantor.unpair rest).1 0) =
      reserve ++ List.replicate (1+padding+(Cantor.unpair rest).1+(Cantor.unpair rest).1+(Cantor.unpair rest).1) 0 := by
    simp only [List.replicate_add, List.replicate_succ, List.replicate_zero,
      List.cons_append, List.nil_append, List.append_assoc]
  have h := ((h1.trans graphSystem hscan).trans graphSystem hem).trans graphSystem hclear
  refine ⟨1+duration+(7*(Cantor.unpair rest).1+3)+(2*(Cantor.unpair rest).1+2),
    1+padding+(Cantor.unpair rest).1+(Cantor.unpair rest).1+(Cantor.unpair rest).1, by omega, ?_⟩
  rw [← hres]
  simpa [unary_as_replicate] using h

def residualTail : Nat → Nat → Nat
  | 0, rest => rest
  | n+1, rest => residualTail n (Cantor.unpair rest).2

theorem residual_tail_pack (xs : List Nat) (tail : Nat) :
    residualTail xs.length (Schedule.packCoordinates xs tail) = tail := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [residualTail, Schedule.packCoordinates, Cantor.unpair_pair, ih]

/-- Any finite residual count emits exactly the schedule's decoded coordinate
list, in order, and returns to the zero-count dispatch with cleared work. -/
theorem residual_coordinates (n : Nat) (base : RegisterMachine.Bank 9) (rest : Nat)
    (reserve : List Nat) (hs : base 0 = 0) :
    ∃ duration padding, n ≤ duration ∧
      graphSystem.Block (cfgRAC 726 (bankOnlyCount base n) rest 0 0 reserve) duration
        (cfgRAC 726 (bankOnlyCount base 0) (residualTail n rest) 0 0
          (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates n rest)) := by
  induction n generalizing rest reserve with
  | zero =>
    refine ⟨0, 0, by omega, ?_⟩
    simpa [residualTail, Schedule.decodeCoordinates, PASoundness.UnaryCodec.encodeFields] using
      WordEventSystem.Block.refl graphSystem (cfgRAC 726 (bankOnlyCount base 0) rest 0 0 reserve)
  | succ n ih =>
    obtain ⟨duration, padding, hd, hfirst⟩ := residual_coordinate_one base n rest reserve hs
    obtain ⟨tailDuration, tailPadding, ht, htail⟩ :=
      ih (Cantor.unpair rest).2 (reserve ++ List.replicate padding 0)
    have h := hfirst.trans graphSystem htail
    refine ⟨duration+tailDuration, padding+tailPadding, by omega, ?_⟩
    have hres : (reserve ++ List.replicate padding 0) ++ List.replicate tailPadding 0 =
        reserve ++ List.replicate (padding+tailPadding) 0 := by
      rw [List.replicate_add]
      simp only [List.append_assoc]
    rw [← hres]
    simpa [residualTail, Schedule.decodeCoordinates, PASoundness.UnaryCodec.encodeFields] using h

/-- After all residual fields, the zero counter takes the branch to entry 749. -/
theorem residual_coordinates_finish (n : Nat) (base : RegisterMachine.Bank 9) (rest : Nat)
    (reserve : List Nat) (hs : base 0 = 0) :
    ∃ duration padding, n+1 ≤ duration ∧
      graphSystem.Block (cfgRAC 726 (bankOnlyCount base n) rest 0 0 reserve) duration
        (cfgRAC 749 (bankOnlyCount base 0) (residualTail n rest) 0 0
          (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates n rest)) := by
  obtain ⟨duration, padding, ht, block⟩ := residual_coordinates n base rest reserve hs
  have hzero := WordEventSystem.Block.single graphSystem
    (residual_count_zero base (residualTail n rest) (reserve ++ List.replicate padding 0))
  refine ⟨duration+1, padding, by omega, ?_⟩
  simpa using block.trans graphSystem hzero

/-- A packed finite coordinate list emits exactly that list and leaves the
arbitrary packed tail intact. -/
theorem residual_coordinates_pack (xs : List Nat) (tail : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hs : base 0 = 0) :
    ∃ duration padding, xs.length+1 ≤ duration ∧
      graphSystem.Block (cfgRAC 726 (bankOnlyCount base xs.length) (Schedule.packCoordinates xs tail) 0 0 reserve) duration
        (cfgRAC 749 (bankOnlyCount base 0) tail 0 0 (reserve ++ List.replicate padding 0))
        (PASoundness.UnaryCodec.encodeFields xs) := by
  simpa [residual_tail_pack, Schedule.decode_pack] using
    residual_coordinates_finish xs.length base (Schedule.packCoordinates xs tail) reserve hs

/-- On a reached prepared entry, the literal selected run emits that entire
finite residual-coordinate word in order and reaches the cleanup boundary. -/
theorem selected_residual_coordinates_finish (i n : Nat) (base : RegisterMachine.Bank 9) (rest : Nat)
    (reserve : List Nat) (hs : base 0 = 0)
    (h : graphSystem.run i = cfgRAC 726 (bankOnlyCount base n) rest 0 0 reserve) :
    ∃ duration padding finish, n+1 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgRAC 749 (bankOnlyCount base 0) (residualTail n rest) 0 0
        (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgRAC 749 (bankOnlyCount base 0) (residualTail n rest) 0 0
        (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates n rest) ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  obtain ⟨duration, padding, ht, block⟩ := residual_coordinates_finish n base rest reserve hs
  have hr : graphSystem.run (i+duration) = cfgRAC 749 (bankOnlyCount base 0) (residualTail n rest) 0 0
      (reserve ++ List.replicate padding 0) := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i ++
      PASoundness.UnaryCodec.encodeFields (Schedule.decodeCoordinates n rest) := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hstate, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, padding, finish, ht, hg, hstate.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · apply graphRefinement.boundary_strict
    omega

/-- The packed-list contract on the selected physical execution, conditional
on reaching the displayed prepared graph entry. -/
theorem selected_residual_coordinates_pack (i : Nat) (xs : List Nat) (tail : Nat)
    (base : RegisterMachine.Bank 9) (reserve : List Nat) (hs : base 0 = 0)
    (h : graphSystem.run i = cfgRAC 726 (bankOnlyCount base xs.length) (Schedule.packCoordinates xs tail) 0 0 reserve) :
    ∃ duration padding finish, xs.length+1 ≤ duration ∧ Good finish ∧
      finish.graphState = cfgRAC 749 (bankOnlyCount base 0) tail 0 0 (reserve ++ List.replicate padding 0) ∧
      graphSystem.run (i+duration) = cfgRAC 749 (bankOnlyCount base 0) tail 0 0 (reserve ++ List.replicate padding 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.encodeFields xs ∧
      graphRefinement.boundary i < graphRefinement.boundary (i+duration) := by
  simpa [residual_tail_pack, Schedule.decode_pack] using
    selected_residual_coordinates_finish i xs.length base (Schedule.packCoordinates xs tail) reserve hs h

end PASoundness.M236.OccurrenceGraph
