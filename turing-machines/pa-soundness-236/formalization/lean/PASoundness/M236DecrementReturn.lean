import PASoundness.M236DecrementSelector
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.DecrementReturn
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

private theorem replicate_shift (n : Nat) (tail : List Bool) :
    List.replicate n true ++ (true :: tail) = true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- State 37 scans an arbitrary run of ones leftward, preserving every cell. -/
theorem scan_ones (count : Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block ⟨37, head, ⟨List.replicate count true ++ left, true :: right⟩⟩ count
      ⟨37, head - (count : Int), ⟨left, true :: (List.replicate count true ++ right)⟩⟩ [] := by
  induction count generalizing head right with
  | zero => simpa using WordEventSystem.Block.refl rawSystem ⟨37, head, ⟨left, true :: right⟩⟩
  | succ count ih =>
    have row : raw.table.row 37 true = ⟨true, .left, 37, false⟩ := by decide
    have event : rawLabels.at 37 true = none := by decide
    have hstep : rawSystem.step
        ⟨37, head, ⟨List.replicate (count + 1) true ++ left, true :: right⟩⟩ =
        (⟨37, head - 1, ⟨List.replicate count true ++ left, true :: true :: right⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row, event,
        Move.apply, moveLeft, List.replicate_succ]
    have hwhole := (WordEventSystem.Block.single rawSystem hstep).trans rawSystem
      (ih (head - 1) (true :: right))
    have ht : 1 + count = count + 1 := by omega
    have hh : head - 1 - (count : Int) = head - ((count + 1 : Nat) : Int) := by omega
    simpa only [List.nil_append, ht, hh, List.replicate_succ, List.cons_append,
      replicate_shift] using hwhole

/-- Starting at a separator, pass one nonempty unary run to the separator
on its left. -/
theorem cross_run (value : Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block
      ⟨37, head, ⟨List.replicate (value + 1) true ++ false :: left, false :: right⟩⟩
      (value + 2)
      ⟨37, head - ((value + 2 : Nat) : Int),
        ⟨left, false :: (List.replicate (value + 1) true ++ false :: right)⟩⟩ [] := by
  have row0 : raw.table.row 37 false = ⟨false, .left, 38, false⟩ := by decide
  have ev0 : rawLabels.at 37 false = none := by decide
  have row1 : raw.table.row 38 true = ⟨true, .left, 37, false⟩ := by decide
  have ev1 : rawLabels.at 38 true = none := by decide
  have hs0 : rawSystem.step
      ⟨37, head, ⟨List.replicate (value + 1) true ++ false :: left, false :: right⟩⟩ =
      (⟨38, head - 1, ⟨List.replicate value true ++ false :: left, true :: false :: right⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row0, ev0,
      Move.apply, moveLeft, List.replicate_succ]
  have hs1 : rawSystem.step
      ⟨38, head - 1, ⟨List.replicate value true ++ false :: left, true :: false :: right⟩⟩ =
      (⟨37, head - 2, ⟨(List.replicate value true ++ false :: left).drop 1,
        (List.replicate value true ++ false :: left).headD false :: true :: false :: right⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row1, ev1,
      Move.apply, moveLeft]
    omega
  cases value with
  | zero =>
    have hb := (WordEventSystem.Block.single rawSystem hs0).trans rawSystem
      (WordEventSystem.Block.single rawSystem hs1)
    simpa using hb
  | succ value =>
    simp only [List.replicate_succ, List.cons_append, List.headD_cons] at hs1
    have hscan := scan_ones value (head - 2) (false :: left) (true :: false :: right)
    have row2 : raw.table.row 37 true = ⟨true, .left, 37, false⟩ := by decide
    have ev2 : rawLabels.at 37 true = none := by decide
    have hs2 : rawSystem.step
        ⟨37, head - 2 - (value : Int),
          ⟨false :: left, true :: (List.replicate value true ++ true :: false :: right)⟩⟩ =
        (⟨37, head - 2 - (value : Int) - 1,
          ⟨left, false :: true :: (List.replicate value true ++ true :: false :: right)⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row2, ev2,
        Move.apply, moveLeft]
    have hwhole := (((WordEventSystem.Block.single rawSystem hs0).trans rawSystem
      (WordEventSystem.Block.single rawSystem hs1)).trans rawSystem hscan).trans rawSystem
      (WordEventSystem.Block.single rawSystem hs2)
    have ht : 1 + 1 + value + 1 = (value + 1) + 2 := by omega
    have hh : head - 2 - (value : Int) - 1 = head - (((value + 1) + 2 : Nat) : Int) := by omega
    simpa only [List.nil_append, ht, hh, List.replicate_succ, List.cons_append,
      replicate_shift] using hwhole

/-- Unary runs in nearest-to-farthest order, each followed by its
left separator. The current separator is represented separately. -/
abbrev leftRuns := UnaryReturn.leftRuns
abbrev pushRuns := UnaryReturn.pushRuns

/-- Traverse every encoded run, with no bound on the number or sizes. -/
theorem cross_runs (values : List Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block ⟨37, head, ⟨leftRuns values ++ left, false :: right⟩⟩
      (shiftTime values)
      ⟨37, head - (shiftTime values : Int), ⟨left, false :: pushRuns values right⟩⟩ [] := by
  induction values generalizing head right with
  | nil => simpa [leftRuns, UnaryReturn.leftRuns, shiftTime, pushRuns, UnaryReturn.pushRuns] using
      WordEventSystem.Block.refl rawSystem ⟨37, head, ⟨left, false :: right⟩⟩
  | cons value rest ih =>
    have hfirst := cross_run value head (leftRuns rest ++ left) right
    have hrest := ih (head - ((value + 2 : Nat) : Int))
      (List.replicate (value + 1) true ++ false :: right)
    have hwhole := hfirst.trans rawSystem hrest
    have hh : head - ((value + 2 : Nat) : Int) - (shiftTime rest : Int) =
        head - ((value + 2 + shiftTime rest : Nat) : Int) := by omega
    simpa only [leftRuns, UnaryReturn.leftRuns, pushRuns, UnaryReturn.pushRuns, shiftTime, List.nil_append, List.cons_append,
      List.append_assoc, hh] using hwhole

/-- After the last run, two adjacent separators take the machine to state 69.
The complete remaining tape and the exact number of silent steps are retained. -/
theorem cross_runs_stop (values : List Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block ⟨37, head, ⟨leftRuns values ++ false :: left, false :: right⟩⟩
      (shiftTime values + 2)
      ⟨69, head - (shiftTime values : Int) - 2,
        moveLeft ⟨left, false :: false :: pushRuns values right⟩ false⟩ [] := by
  have hb := cross_runs values head (false :: left) right
  have row0 : raw.table.row 37 false = ⟨false, .left, 38, false⟩ := by decide
  have ev0 : rawLabels.at 37 false = none := by decide
  have row1 : raw.table.row 38 false = ⟨false, .left, 69, false⟩ := by decide
  have ev1 : rawLabels.at 38 false = none := by decide
  have hs0 : rawSystem.step ⟨37, head - (shiftTime values : Int),
      ⟨false :: left, false :: pushRuns values right⟩⟩ =
      (⟨38, head - (shiftTime values : Int) - 1,
        ⟨left, false :: false :: pushRuns values right⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row0, ev0,
      Move.apply, moveLeft]
  have hs1 : rawSystem.step ⟨38, head - (shiftTime values : Int) - 1,
      ⟨left, false :: false :: pushRuns values right⟩⟩ =
      (⟨69, head - (shiftTime values : Int) - 2,
        moveLeft ⟨left, false :: false :: pushRuns values right⟩ false⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row1, ev1,
      Move.apply]
    omega
  simpa [Nat.add_assoc] using (hb.trans rawSystem
    (WordEventSystem.Block.single rawSystem hs0)).trans rawSystem
      (WordEventSystem.Block.single rawSystem hs1)



/-- For the zero branch, scan the entire preceding bank back to the double
separator, reaching the literal state 69 while retaining all tape cells. -/
theorem physical_zero_return (r : Fin 9) (gap : Nat) (before : List Nat)
    (hlen : before.length = r.val) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨DecrementSelector.entryState r, head,
      ⟨left, true :: false :: (bank (gap :: before) ++ true :: false :: tail)⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c
        (shiftTime (gap :: before) + 2 + 3 + (shiftTime (gap :: before).reverse + 2)) finish [] ∧
      Related ⟨69, head + 2 + (shiftTime (gap :: before) : Int) - 1 -
          (shiftTime (gap :: before).reverse : Int) - 2,
        moveLeft ⟨left, false :: false ::
          (bank (gap :: before) ++ true :: false :: tail)⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (shiftTime (gap :: before) + 2 + 3 + (shiftTime (gap :: before).reverse + 2))
        (mapConfig finish) [] ∧
      0 < shiftTime (gap :: before) + 2 + 3 + (shiftTime (gap :: before).reverse + 2) := by
  obtain ⟨middle, hp, hr, hq, ht⟩ :=
    DecrementSelector.physical_zero_test r gap before hlen head left tail c hrel
  have hbank := UnaryReturn.bank_reverse_boundary (gap :: before) (false :: left)
  rw [hbank] at hr
  have hr' : Related ⟨37, head + 2 + (shiftTime (gap :: before) : Int) - 1,
      ⟨leftRuns (gap :: before).reverse ++ false :: left, false :: true :: false :: tail⟩⟩ middle := by
    simpa [moveLeft] using hr
  have hb := cross_runs_stop (gap :: before).reverse
    (head + 2 + (shiftTime (gap :: before) : Int) - 1) left (true :: false :: tail)
  have hpush : pushRuns (gap :: before).reverse (true :: false :: tail) =
      bank (gap :: before) ++ true :: false :: tail := by
    simpa [pushRuns] using UnaryReturn.pushRuns_bank (gap :: before).reverse (true :: false :: tail)
  rw [hpush] at hb
  obtain ⟨finish, hpr, hrr⟩ := BulkSweep.physical_block raw rawLabels _ _ middle _ hr' hb
  refine ⟨finish, ?_, hrr, ?_, by omega⟩
  · simpa using hp.trans (machineWordSystem raw rawLabels) hpr
  · simpa using hq.trans (machineWordSystem machine machineLabels) (BootstrapScan.mapped_block hpr)

example : rawSystem.Block ⟨57, 0, ⟨[], [true, false, true, false, true, false]⟩⟩ 11
    ⟨69, -1, ⟨[], [false, false, false, true, false, true, false]⟩⟩ [] := by
  constructor <;> decide

example : ¬ rawSystem.Block ⟨57, 0, ⟨[], [true, false, true, false, true, false]⟩⟩ 10
    ⟨69, -1, ⟨[], [false, false, false, true, false, true, false]⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance ⟨57, 0, ⟨[], [true, false, true, false, true, false]⟩⟩ 10 ≠
    ⟨69, -1, ⟨[], [false, false, false, true, false, true, false]⟩⟩ := by decide
  exact bad h.endpoint
end PASoundness.M236.DecrementReturn
