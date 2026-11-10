import PASoundness.M236DecrementSeek
import PASoundness.M236DecrementReturn
import PASoundness.M236SelectorRoot
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.DecrementShift
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

private theorem true_shift (n : Nat) (tail : List Bool) :
    List.replicate n true ++ true :: tail = true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- State 31 crosses a finite run leftward without changing it. -/
theorem scan_ones (count : Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block ⟨31, head, ⟨List.replicate count true ++ left, true :: right⟩⟩ count
      ⟨31, head - (count : Int), ⟨left, true :: (List.replicate count true ++ right)⟩⟩ [] := by
  induction count generalizing head right with
  | zero => simpa using WordEventSystem.Block.refl rawSystem ⟨31, head, ⟨left, true :: right⟩⟩
  | succ count ih =>
    have row : raw.table.row 31 true = ⟨true, .left, 31, false⟩ := by decide
    have event : rawLabels.at 31 true = none := by decide
    have hstep : rawSystem.step
        ⟨31, head, ⟨List.replicate (count + 1) true ++ left, true :: right⟩⟩ =
        (⟨31, head - 1, ⟨List.replicate count true ++ left, true :: true :: right⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row, event,
        Move.apply, moveLeft, List.replicate_succ]
    have hb := (WordEventSystem.Block.single rawSystem hstep).trans rawSystem (ih (head - 1) (true :: right))
    have hh : head - 1 - (count : Int) = head - ((count + 1 : Nat) : Int) := by omega
    simpa only [List.nil_append, hh, Nat.add_comm 1 count, List.replicate_succ,
      List.cons_append, true_shift] using hb

/-- State 31 shifts one unary separator left by one cell. -/
theorem shift_run (value : Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block
      ⟨31, head, ⟨List.replicate (value + 1) true ++ false :: left, false :: right⟩⟩
      (value + 2)
      ⟨31, head - ((value + 2 : Nat) : Int),
        ⟨left, false :: (List.replicate value true ++ false :: true :: right)⟩⟩ [] := by
  have row0 : raw.table.row 31 false = ⟨true, .left, 32, false⟩ := by decide
  have ev0 : rawLabels.at 31 false = none := by decide
  have row1 : raw.table.row 32 true = ⟨false, .left, 31, false⟩ := by decide
  have ev1 : rawLabels.at 32 true = none := by decide
  have hs0 : rawSystem.step
      ⟨31, head, ⟨List.replicate (value + 1) true ++ false :: left, false :: right⟩⟩ =
      (⟨32, head - 1, ⟨List.replicate value true ++ false :: left, true :: true :: right⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row0, ev0,
      Move.apply, moveLeft, List.replicate_succ]
  have hs1 : rawSystem.step
      ⟨32, head - 1, ⟨List.replicate value true ++ false :: left, true :: true :: right⟩⟩ =
      (⟨31, head - 2, ⟨(List.replicate value true ++ false :: left).drop 1,
        (List.replicate value true ++ false :: left).headD false :: false :: true :: right⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row1, ev1,
      Move.apply, moveLeft]
    omega
  cases value with
  | zero =>
    have hb := (WordEventSystem.Block.single rawSystem hs0).trans rawSystem (WordEventSystem.Block.single rawSystem hs1)
    simpa using hb
  | succ value =>
    simp only [List.replicate_succ, List.cons_append, List.headD_cons] at hs1
    have hscan := scan_ones value (head - 2) (false :: left) (false :: true :: right)
    have row2 : raw.table.row 31 true = ⟨true, .left, 31, false⟩ := by decide
    have ev2 : rawLabels.at 31 true = none := by decide
    have hs2 : rawSystem.step
        ⟨31, head - 2 - (value : Int),
          ⟨false :: left, true :: (List.replicate value true ++ false :: true :: right)⟩⟩ =
        (⟨31, head - 2 - (value : Int) - 1,
          ⟨left, false :: true :: (List.replicate value true ++ false :: true :: right)⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row2, ev2, Move.apply, moveLeft]
    have hb := (((WordEventSystem.Block.single rawSystem hs0).trans rawSystem
      (WordEventSystem.Block.single rawSystem hs1)).trans rawSystem hscan).trans rawSystem
      (WordEventSystem.Block.single rawSystem hs2)
    have ht : 1 + 1 + value + 1 = (value + 1) + 2 := by omega
    have hh : head - 2 - (value : Int) - 1 = head - (((value + 1) + 2 : Nat) : Int) := by omega
    simpa only [List.nil_append, ht, hh, List.replicate_succ, List.cons_append, true_shift] using hb

def pushShift : List Nat → List Bool → List Bool
  | [], right => right
  | value :: rest, right => pushShift rest (List.replicate value true ++ false :: true :: right)

/-- Every finite sequence of unary runs is shifted backward in finite time. -/
theorem shift_runs (values : List Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block ⟨31, head, ⟨UnaryReturn.leftRuns values ++ left, false :: right⟩⟩
      (shiftTime values)
      ⟨31, head - (shiftTime values : Int), ⟨left, false :: pushShift values right⟩⟩ [] := by
  induction values generalizing head right with
  | nil => simpa [UnaryReturn.leftRuns, shiftTime, pushShift] using
      WordEventSystem.Block.refl rawSystem ⟨31, head, ⟨left, false :: right⟩⟩
  | cons value rest ih =>
    have hs := shift_run value head (UnaryReturn.leftRuns rest ++ left) right
    have hr := ih (head - ((value + 2 : Nat) : Int))
      (List.replicate value true ++ false :: true :: right)
    have hb := hs.trans rawSystem hr
    have hh : head - ((value + 2 : Nat) : Int) - (shiftTime rest : Int) =
        head - ((value + 2 + shiftTime rest : Nat) : Int) := by omega
    simpa only [UnaryReturn.leftRuns, pushShift, shiftTime, List.nil_append, List.cons_append,
      List.append_assoc, hh] using hb

/-- The double-zero boundary terminates the backward shift at state 35. -/
theorem shift_runs_stop (values : List Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block ⟨31, head, ⟨UnaryReturn.leftRuns values ++ false :: left, false :: right⟩⟩
      (shiftTime values + 2)
      ⟨35, head - (shiftTime values : Int) - 2,
        moveLeft ⟨left, false :: true :: pushShift values right⟩ false⟩ [] := by
  have hs := shift_runs values head (false :: left) right
  have r31 : raw.table.row 31 false = ⟨true, .left, 32, false⟩ := by decide
  have e31 : rawLabels.at 31 false = none := by decide
  have r32 : raw.table.row 32 false = ⟨false, .left, 35, false⟩ := by decide
  have e32 : rawLabels.at 32 false = none := by decide
  have h0 : rawSystem.step ⟨31, head - (shiftTime values : Int),
      ⟨false :: left, false :: pushShift values right⟩⟩ =
      (⟨32, head - (shiftTime values : Int) - 1,
        ⟨left, false :: true :: pushShift values right⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r31, e31, Move.apply, moveLeft]
  have h1 : rawSystem.step ⟨32, head - (shiftTime values : Int) - 1,
      ⟨left, false :: true :: pushShift values right⟩⟩ =
      (⟨35, head - (shiftTime values : Int) - 2,
        moveLeft ⟨left, false :: true :: pushShift values right⟩ false⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r32, e32, Move.apply]
    omega
  simpa [Nat.add_assoc] using (hs.trans rawSystem (WordEventSystem.Block.single rawSystem h0)).trans rawSystem
    (WordEventSystem.Block.single rawSystem h1)

theorem seekLeft_reverse (values : List Nat) (left : List Bool) :
    DecrementSeek.seekLeft values left = UnaryReturn.leftRuns values.reverse ++ left := by
  induction values generalizing left with
  | nil => rfl
  | cons value rest ih =>
    simp [DecrementSeek.seekLeft, ih, List.reverse_cons, UnaryReturn.leftRuns_append,
      UnaryReturn.leftRuns, List.replicate_succ, List.append_assoc, true_shift]

theorem pushShift_append (xs ys : List Nat) (right : List Bool) :
    pushShift (xs ++ ys) right = pushShift ys (pushShift xs right) := by
  induction xs generalizing right with
  | nil => rfl
  | cons value rest ih => simpa [pushShift] using ih (List.replicate value true ++ false :: true :: right)

/-- The backward shift retains an additional zero-valued unary block at the
right edge; this exact tail is not silently identified with a blank cell. -/
theorem pushShift_reverse_bank (values : List Nat) (tail : List Bool) :
    true :: pushShift values.reverse (false :: tail) = bank values ++ true :: false :: tail := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.reverse_cons, pushShift_append, pushShift, bank, List.cons_append]
    rw [ih]
    simp [List.append_assoc]

theorem pushShift_selected (value : Nat) (after : List Nat) (tail : List Bool) :
    true :: pushShift (after.reverse ++ [value]) (false :: tail) =
      bank (value :: after) ++ true :: false :: tail := by
  rw [pushShift_append]
  simp only [pushShift, bank, List.cons_append]
  rw [pushShift_reverse_bank]
  simp [List.append_assoc]

/-- The positive branch shifts an arbitrary finite suffix back to state 35.
The exact extra zero-valued block at the right edge is explicit. -/
theorem positive_shift (value : Nat) (after : List Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨8, head,
      ⟨false :: left, true :: true :: (List.replicate value true ++ false :: (bank after ++ false :: tail))⟩⟩
      ((2 + value + (shiftTime after + 2)) + (shiftTime (after.reverse ++ [value]) + 2))
      ⟨35, head + 2 + (value : Int) + (shiftTime after : Int) -
          (shiftTime (after.reverse ++ [value]) : Int) - 2,
        moveLeft ⟨left, false :: (bank (value :: after) ++ true :: false :: tail)⟩ false⟩ [] := by
  have hs := DecrementSeek.positive_seek value after head (false :: left) tail
  have hl : DecrementSeek.seekLeft after (List.replicate value true ++ true :: false :: false :: left) =
      UnaryReturn.leftRuns (after.reverse ++ [value]) ++ false :: left := by
    rw [seekLeft_reverse, UnaryReturn.leftRuns_append]
    simp [UnaryReturn.leftRuns, List.replicate_succ, List.append_assoc, true_shift]
  rw [hl] at hs
  have hb := shift_runs_stop (after.reverse ++ [value])
    (head + 2 + (value : Int) + (shiftTime after : Int)) left (false :: tail)
  rw [pushShift_selected] at hb
  simpa only [List.nil_append] using hs.trans rawSystem hb

/-- From a prepared positive decrement entry, selection, suffix scan and
backward shift reach state 35 on both literal tables. -/
theorem physical_positive_shift (r : Fin 9) (gap : Nat) (before : List Nat)
    (hlen : before.length = r.val) (value : Nat) (after : List Nat)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨DecrementSelector.entryState r, head,
      ⟨left, true :: false :: (bank (gap :: before) ++ true :: true ::
        (List.replicate value true ++ false :: (bank after ++ false :: tail)))⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c
        ((shiftTime (gap :: before) + 2) +
          ((2 + value + (shiftTime after + 2)) + (shiftTime (after.reverse ++ [value]) + 2))) finish [] ∧
      Related ⟨35, head + 2 + (shiftTime (gap :: before) : Int) + 2 + (value : Int) +
          (shiftTime after : Int) - (shiftTime (after.reverse ++ [value]) : Int) - 2,
        moveLeft ⟨UnaryReturn.leftRuns (gap :: before).reverse ++ false :: left,
          false :: (bank (value :: after) ++ true :: false :: tail)⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((shiftTime (gap :: before) + 2) +
          ((2 + value + (shiftTime after + 2)) + (shiftTime (after.reverse ++ [value]) + 2))) (mapConfig finish) [] ∧
      0 < (shiftTime (gap :: before) + 2) +
        ((2 + value + (shiftTime after + 2)) + (shiftTime (after.reverse ++ [value]) + 2)) := by
  have hs := DecrementSelector.entry_block r gap before hlen head left
    (true :: true :: (List.replicate value true ++ false :: (bank after ++ false :: tail)))
  have hl := UnaryReturn.bank_reverse_boundary (gap :: before) (false :: left)
  rw [hl] at hs
  have hb := positive_shift value after (head + 2 + (shiftTime (gap :: before) : Int))
    (UnaryReturn.leftRuns (gap :: before).reverse ++ false :: left) tail
  have ht := hs.trans rawSystem hb
  simp only [List.nil_append] at ht
  obtain ⟨finish, hp, hr⟩ := BulkSweep.physical_block raw rawLabels _ _ c _ hrel ht
  exact ⟨finish, hp, hr, BootstrapScan.mapped_block hp, by omega⟩

/-- The positive branch returns across the preceding bank to state 68. The
new terminal zero block is retained in the exact output tape. -/
theorem physical_positive_return (r : Fin 9) (gap : Nat) (before : List Nat)
    (hlen : before.length = r.val) (value : Nat) (after : List Nat)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨DecrementSelector.entryState r, head,
      ⟨left, true :: false :: (bank (gap :: before) ++ true :: true ::
        (List.replicate value true ++ false :: (bank after ++ false :: tail)))⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (finish : Config 237),
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨68, endHead,
        moveLeft ⟨left, false :: false ::
          (bank (gap :: (before ++ value :: (after ++ [0]))) ++ tail)⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  obtain ⟨mid, hp, hr, hq, ht⟩ := physical_positive_shift r gap before hlen value after head left tail c hrel
  cases hv : (gap :: before).reverse with
  | nil => simp at hv
  | cons first values =>
    rw [hv] at hr
    let h35 := head + 2 + (shiftTime (gap :: before) : Int) + 2 + (value : Int) +
      (shiftTime after : Int) - (shiftTime (after.reverse ++ [value]) : Int) - 2
    have hb := UnaryReturn.return_nonempty first values h35 left
      (bank (value :: after) ++ true :: false :: tail)
    obtain ⟨finish, hpr, hrr⟩ := BulkSweep.physical_block raw rawLabels _ _ mid _ hr hb
    have he : values.reverse ++ [first] = gap :: before := by
      have h := congrArg List.reverse hv
      simpa [List.reverse_cons, List.reverse_reverse] using h.symm
    have hpush : UnaryReturn.pushRuns values
        (List.replicate (first + 1) true ++ false :: (bank (value :: after) ++ true :: false :: tail)) =
        bank (gap :: (before ++ value :: (after ++ [0]))) ++ tail := by
      rw [UnaryReturn.pushRuns_bank]
      have hfirst : bank values.reverse ++
          (List.replicate (first + 1) true ++ false :: (bank (value :: after) ++ true :: false :: tail)) =
          bank (values.reverse ++ [first]) ++ (bank (value :: after) ++ true :: false :: tail) := by
        simp [UnaryIncrement.bank_append, bank, List.replicate_succ, List.append_assoc]
      rw [hfirst, he]
      simp [UnaryIncrement.bank_append, bank, List.append_assoc]
    rw [hpush] at hrr
    let t1 := (shiftTime (gap :: before) + 2) +
      ((2 + value + (shiftTime after + 2)) + (shiftTime (after.reverse ++ [value]) + 2))
    let t2 := first + 1 + (shiftTime values + 2)
    refine ⟨t1 + t2, h35 - ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2,
      finish, ?_, ?_, hrr, ?_⟩
    · dsimp [t1, t2]; omega
    · simpa [t1, t2] using hp.trans (machineWordSystem raw rawLabels) hpr
    · simpa [t1, t2] using hq.trans (machineWordSystem machine machineLabels) (BootstrapScan.mapped_block hpr)

/-- A prepared positive decrement returns to the grammar root. Its exact
bank includes the extra terminal zero block created by the backward shift. -/
theorem physical_positive_root (r : Fin 9) (gap scratch : Nat) (before after : List Nat)
    (hlen : before.length = r.val) (value : Nat) (runs : List (Fin 6))
    (bit : Bool) (pcTail : List Bool) (hprefix : counterPush runs [] = true :: bit :: pcTail)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨DecrementSelector.entryState r, head,
      ⟨List.replicate scratch true ++ false :: (counterWord runs ++ List.replicate 6 false ++ false :: left),
        true :: false :: (bank (gap :: before) ++ true :: true ::
          (List.replicate value true ++ false :: (bank after ++ false :: tail)))⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (finish : Config 237),
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + scratch + 2) false ++ true :: false ::
            (bank (before ++ value :: (after ++ [0])) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  let pre := counterWord runs ++ List.replicate 6 false ++ false :: left
  let values := before ++ value :: (after ++ [0])
  let suffix := List.replicate (gap + scratch + 2) false ++ true :: false :: (bank values ++ tail)
  obtain ⟨t1, h68, mid1, ht1, hp1, hr1, hq1⟩ :=
    physical_positive_return r gap before hlen value after head
      (List.replicate scratch true ++ false :: pre) tail c hrel
  obtain ⟨mid2, hp2, hr2, hq2, ht2⟩ :=
    SelectorReturn.physical_filled_cleanup gap scratch values h68 pre tail mid1 hr1
  let h64 := h68 - (scratch : Int) - 1
  obtain ⟨mid3, hp3, hr3, hq3, ht3⟩ := physical_counter runs h64 (false :: left) suffix mid2 hr2
  have hcontrol : counterPush runs suffix = true :: bit :: (pcTail ++ suffix) := by
    have h := counterPush_append runs [] suffix
    simpa [hprefix] using h
  rw [hcontrol] at hr3
  let h65 := h64 - (counterTime runs : Int) - 6
  have hroot : Related ⟨65, h65,
      ⟨left, List.replicate 7 false ++ true :: true :: bit :: (pcTail ++ suffix)⟩⟩ mid3 := by
    simpa [h65, moveLeft, List.replicate_succ] using hr3
  have hb := root_reentry 7 bit h65 left (pcTail ++ suffix)
  obtain ⟨finish, hp4, hr4⟩ := BulkSweep.physical_block raw rawLabels _ _ mid3 10 hroot hb
  let t2 := 3 * scratch + 2 * gap + 9
  refine ⟨t1 + t2 + (counterTime runs + 6) + 10, h65 + 10, finish, ?_, ?_, ?_, ?_⟩
  · dsimp [t2]; omega
  · simpa [t2] using ((hp1.trans (machineWordSystem raw rawLabels) hp2).trans
      (machineWordSystem raw rawLabels) hp3).trans (machineWordSystem raw rawLabels) hp4
  · simpa [h65, h64, suffix, values, Int.add_assoc] using hr4
  · simpa [t2] using ((hq1.trans (machineWordSystem machine machineLabels) hq2).trans
      (machineWordSystem machine machineLabels) hq3).trans (machineWordSystem machine machineLabels)
        (BootstrapScan.mapped_block hp4)

/-- The independent positive decrement updates exactly the selected register. -/
theorem values_decrement (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (value : Nat) (hvalue : registers r = value + 1) :
    UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank =
      UnaryIncrementNine.before registers r ++ value :: UnaryIncrementNine.after registers r := by
  rw [RegisterMachine.decNZ_succ registers r value hvalue]
  change UnaryNine.values (RegisterMachine.write registers r value) = _
  rw [UnaryIncrementNine.values_write, List.set_eq_take_append_cons_drop]
  have hi : r.val < (UnaryNine.values registers).length := by simp [r.isLt]
  simp only [hi, ↓reduceIte, UnaryIncrementNine.before, UnaryIncrementNine.after]

/-- A prepared positive named decrement returns to the root with the selected
register decremented and every other register unchanged. The exact physical
reserve has one extra zero-valued block. The source control branch and blank
start remain separate obligations. -/
theorem physical_named_positive_root (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (value : Nat) (hvalue : registers r = value + 1) (reserve : List Nat) (gap scratch : Nat)
    (runs : List (Fin 6)) (bit : Bool) (pcTail : List Bool)
    (hprefix : counterPush runs [] = true :: bit :: pcTail)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨DecrementSelector.entryState r, head,
      ⟨List.replicate scratch true ++ false :: (counterWord runs ++ List.replicate 6 false ++ false :: left),
        true :: false :: (bank (gap :: UnaryIncrementNine.before registers r) ++ true :: true ::
          (List.replicate value true ++ false ::
            (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail)))⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (finish : Config 237),
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + scratch + 2) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + (reserve ++ [0]).length)
        (bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0]), tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨RegisterMachine.write registers r value, true, []⟩ := by
  obtain ⟨time, endHead, finish, ht, hp, hr, hq⟩ :=
    physical_positive_root r gap scratch (UnaryIncrementNine.before registers r)
      (UnaryIncrementNine.after registers r ++ reserve) (Selector.before_length registers r)
      value runs bit pcTail hprefix head left tail c hrel
  have hv : UnaryIncrementNine.before registers r ++ value ::
      ((UnaryIncrementNine.after registers r ++ reserve) ++ [0]) =
      UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0]) := by
    rw [values_decrement registers r value hvalue]
    simp [List.append_assoc]
  rw [hv] at hr
  refine ⟨time, endHead, finish, ht, hp, hr, hq, ?_, RegisterMachine.decNZ_succ registers r value hvalue⟩
  have hlen' : (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])).length =
      9 + (reserve ++ [0]).length := by rw [List.length_append, UnaryNine.values_length]
  rw [← hlen']
  exact UnaryCodec.decode_bank (UnaryNine.values (RegisterMachine.execute (.decNZ r) registers).bank ++ (reserve ++ [0])) tail

example : rawSystem.Block
    ⟨57, 0, ⟨[false, false, true, true, false, false, false, false, false, false, false],
      [true, false, true, false, true, true, false] ++ bank (List.replicate 8 0) ++ [false]⟩⟩ 75
    ⟨79, -1, ⟨[false, true, true, false, false, false, false, false, false, false],
      [true, false, false, true, false] ++ bank (List.replicate 10 0)⟩⟩ [] := by
  constructor <;> decide

example : ¬ rawSystem.Block
    ⟨57, 0, ⟨[false, false, true, true, false, false, false, false, false, false, false],
      [true, false, true, false, true, true, false] ++ bank (List.replicate 8 0) ++ [false]⟩⟩ 74
    ⟨79, -1, ⟨[false, true, true, false, false, false, false, false, false, false],
      [true, false, false, true, false] ++ bank (List.replicate 10 0)⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance
      ⟨57, 0, ⟨[false, false, true, true, false, false, false, false, false, false, false],
        [true, false, true, false, true, true, false] ++ bank (List.replicate 8 0) ++ [false]⟩⟩ 74 ≠
      ⟨79, -1, ⟨[false, true, true, false, false, false, false, false, false, false],
        [true, false, false, true, false] ++ bank (List.replicate 10 0)⟩⟩ := by decide
  exact bad h.endpoint
end PASoundness.M236.DecrementShift
