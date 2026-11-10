import PASoundness.M236UnaryIncrementNine

/-! The literal increment return scans left over arbitrary unary runs until
it sees two adjacent zero cells. The meaning of state 68 and source control
is not assumed here. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.UnaryReturn
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

private theorem replicate_shift (n : Nat) (tail : List Bool) :
    List.replicate n true ++ (true :: tail) = true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- State 35 scans an arbitrary run of ones leftward, preserving every cell. -/
theorem scan_ones (count : Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block ⟨35, head, ⟨List.replicate count true ++ left, true :: right⟩⟩ count
      ⟨35, head - (count : Int), ⟨left, true :: (List.replicate count true ++ right)⟩⟩ [] := by
  induction count generalizing head right with
  | zero => simpa using WordEventSystem.Block.refl rawSystem ⟨35, head, ⟨left, true :: right⟩⟩
  | succ count ih =>
    have row : raw.table.row 35 true = ⟨true, .left, 35, false⟩ := by decide
    have event : rawLabels.at 35 true = none := by decide
    have hstep : rawSystem.step
        ⟨35, head, ⟨List.replicate (count + 1) true ++ left, true :: right⟩⟩ =
        (⟨35, head - 1, ⟨List.replicate count true ++ left, true :: true :: right⟩⟩, []) := by
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
      ⟨35, head, ⟨List.replicate (value + 1) true ++ false :: left, false :: right⟩⟩
      (value + 2)
      ⟨35, head - ((value + 2 : Nat) : Int),
        ⟨left, false :: (List.replicate (value + 1) true ++ false :: right)⟩⟩ [] := by
  have row0 : raw.table.row 35 false = ⟨false, .left, 36, false⟩ := by decide
  have ev0 : rawLabels.at 35 false = none := by decide
  have row1 : raw.table.row 36 true = ⟨true, .left, 35, false⟩ := by decide
  have ev1 : rawLabels.at 36 true = none := by decide
  have hs0 : rawSystem.step
      ⟨35, head, ⟨List.replicate (value + 1) true ++ false :: left, false :: right⟩⟩ =
      (⟨36, head - 1, ⟨List.replicate value true ++ false :: left, true :: false :: right⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row0, ev0,
      Move.apply, moveLeft, List.replicate_succ]
  have hs1 : rawSystem.step
      ⟨36, head - 1, ⟨List.replicate value true ++ false :: left, true :: false :: right⟩⟩ =
      (⟨35, head - 2, ⟨(List.replicate value true ++ false :: left).drop 1,
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
    have row2 : raw.table.row 35 true = ⟨true, .left, 35, false⟩ := by decide
    have ev2 : rawLabels.at 35 true = none := by decide
    have hs2 : rawSystem.step
        ⟨35, head - 2 - (value : Int),
          ⟨false :: left, true :: (List.replicate value true ++ true :: false :: right)⟩⟩ =
        (⟨35, head - 2 - (value : Int) - 1,
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
def leftRuns : List Nat → List Bool
  | [] => []
  | value :: rest => List.replicate (value + 1) true ++ false :: leftRuns rest

def pushRuns : List Nat → List Bool → List Bool
  | [], right => right
  | value :: rest, right =>
      pushRuns rest (List.replicate (value + 1) true ++ false :: right)

/-- Traverse every encoded run, with no bound on the number or sizes. -/
theorem cross_runs (values : List Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block ⟨35, head, ⟨leftRuns values ++ left, false :: right⟩⟩
      (shiftTime values)
      ⟨35, head - (shiftTime values : Int), ⟨left, false :: pushRuns values right⟩⟩ [] := by
  induction values generalizing head right with
  | nil => simpa [leftRuns, shiftTime, pushRuns] using
      WordEventSystem.Block.refl rawSystem ⟨35, head, ⟨left, false :: right⟩⟩
  | cons value rest ih =>
    have hfirst := cross_run value head (leftRuns rest ++ left) right
    have hrest := ih (head - ((value + 2 : Nat) : Int))
      (List.replicate (value + 1) true ++ false :: right)
    have hwhole := hfirst.trans rawSystem hrest
    have hh : head - ((value + 2 : Nat) : Int) - (shiftTime rest : Int) =
        head - ((value + 2 + shiftTime rest : Nat) : Int) := by omega
    simpa only [leftRuns, pushRuns, shiftTime, List.nil_append, List.cons_append,
      List.append_assoc, hh] using hwhole

/-- After the last run, two adjacent separators take the machine to state 68.
The complete remaining tape and the exact number of silent steps are retained. -/
theorem cross_runs_stop (values : List Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block ⟨35, head, ⟨leftRuns values ++ false :: left, false :: right⟩⟩
      (shiftTime values + 2)
      ⟨68, head - (shiftTime values : Int) - 2,
        moveLeft ⟨left, false :: false :: pushRuns values right⟩ false⟩ [] := by
  have hb := cross_runs values head (false :: left) right
  have row0 : raw.table.row 35 false = ⟨false, .left, 36, false⟩ := by decide
  have ev0 : rawLabels.at 35 false = none := by decide
  have row1 : raw.table.row 36 false = ⟨false, .left, 68, false⟩ := by decide
  have ev1 : rawLabels.at 36 false = none := by decide
  have hs0 : rawSystem.step ⟨35, head - (shiftTime values : Int),
      ⟨false :: left, false :: pushRuns values right⟩⟩ =
      (⟨36, head - (shiftTime values : Int) - 1,
        ⟨left, false :: false :: pushRuns values right⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row0, ev0,
      Move.apply, moveLeft]
  have hs1 : rawSystem.step ⟨36, head - (shiftTime values : Int) - 1,
      ⟨left, false :: false :: pushRuns values right⟩⟩ =
      (⟨68, head - (shiftTime values : Int) - 2,
        moveLeft ⟨left, false :: false :: pushRuns values right⟩ false⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row1, ev1,
      Move.apply]
    omega
  simpa [Nat.add_assoc] using (hb.trans rawSystem
    (WordEventSystem.Block.single rawSystem hs0)).trans rawSystem
      (WordEventSystem.Block.single rawSystem hs1)

/-- The block also holds for the infinite physical tapes of the raw table
and its event-preserving selected quotient. -/
theorem physical_return (values : List Nat) (head : Int) (left right : List Bool)
    (c : Config 237)
    (hrel : Related ⟨35, head, ⟨leftRuns values ++ false :: left, false :: right⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (shiftTime values + 2) finish [] ∧
      Related ⟨68, head - (shiftTime values : Int) - 2,
        moveLeft ⟨left, false :: false :: pushRuns values right⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (shiftTime values + 2)
        (mapConfig finish) [] ∧ 0 < shiftTime values + 2 := by
  have hb := cross_runs_stop values head left right
  have hs := advance_sound raw rawLabels hrel (shiftTime values + 2)
  change Related (rawSystem.advance
      ⟨35, head, ⟨leftRuns values ++ false :: left, false :: right⟩⟩
      (shiftTime values + 2)) _ ∧
    rawSystem.wordFrom ⟨35, head, ⟨leftRuns values ++ false :: left, false :: right⟩⟩
      (shiftTime values + 2) = _ at hs
  rw [hb.endpoint, hb.output] at hs
  let finish := (machineWordSystem raw rawLabels).advance c (shiftTime values + 2)
  have hp : (machineWordSystem raw rawLabels).Block c (shiftTime values + 2) finish [] :=
    ⟨rfl, hs.2.symm⟩
  exact ⟨finish, hp, hs.1, BootstrapScan.mapped_block hp, by omega⟩

theorem leftRuns_append (xs ys : List Nat) :
    leftRuns (xs ++ ys) = leftRuns xs ++ leftRuns ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [leftRuns, ih, List.append_assoc]

theorem shifted_reverse (values : List Nat) :
    (shiftedWord values).reverse = leftRuns values.reverse := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp [shiftedWord, leftRuns_append, leftRuns, ih, List.reverse_append,
      List.reverse_replicate, List.append_assoc]

theorem bank_reverse_boundary (values : List Nat) (left : List Bool) :
    (bank values).reverse ++ false :: left = false :: (leftRuns values.reverse ++ left) := by
  induction values generalizing left with
  | nil => rfl
  | cons value rest ih =>
    simp only [bank, List.reverse_cons, List.reverse_append, List.reverse_replicate,
      List.append_assoc, List.cons_append]
    rw [ih]
    simp [leftRuns_append, leftRuns, List.replicate_succ, List.append_assoc, replicate_shift]

/-- The shift endpoint consists of a nonempty reversed unary bank followed by
the left boundary cell, when that boundary is present at entry. -/
theorem increment_shifted_left (before : List Nat) (value : Nat) (rest : List Nat)
    (left : List Bool) :
    shiftedLeft rest (true :: (List.replicate (value + 1) true ++
        ((bank before).reverse ++ false :: false :: left))) =
      leftRuns (rest.reverse ++ (value + 1) :: before.reverse) ++ false :: left := by
  rw [shiftedLeft_eq, shifted_reverse, bank_reverse_boundary, leftRuns_append]
  simp [leftRuns, List.replicate_succ, List.append_assoc]

/-- Starting on the last one of a nonempty reversed bank, return to the
left boundary and enter state 68. -/
theorem return_nonempty (value : Nat) (values : List Nat) (head : Int)
    (left right : List Bool) :
    rawSystem.Block
      ⟨35, head, moveLeft ⟨leftRuns (value :: values) ++ false :: left, false :: right⟩ false⟩
      (value + 1 + (shiftTime values + 2))
      ⟨68, head - ((value + 1 : Nat) : Int) - (shiftTime values : Int) - 2,
        moveLeft ⟨left, false :: false ::
          pushRuns values (List.replicate (value + 1) true ++ false :: right)⟩ false⟩ [] := by
  have hscan := scan_ones value head (false :: (leftRuns values ++ false :: left)) (false :: right)
  have row : raw.table.row 35 true = ⟨true, .left, 35, false⟩ := by decide
  have ev : rawLabels.at 35 true = none := by decide
  have hs : rawSystem.step
      ⟨35, head - (value : Int),
        ⟨false :: (leftRuns values ++ false :: left),
          true :: (List.replicate value true ++ false :: right)⟩⟩ =
      (⟨35, head - (value : Int) - 1,
        ⟨leftRuns values ++ false :: left,
          false :: (List.replicate (value + 1) true ++ false :: right)⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row, ev,
      Move.apply, moveLeft, List.replicate_succ]
  have hrest := cross_runs_stop values (head - (value : Int) - 1) left
    (List.replicate (value + 1) true ++ false :: right)
  have hwhole := (hscan.trans rawSystem (WordEventSystem.Block.single rawSystem hs)).trans rawSystem hrest
  have hh : head - (value : Int) - 1 - (shiftTime values : Int) - 2 =
      head - ((value + 1 : Nat) : Int) - (shiftTime values : Int) - 2 := by omega
  simpa only [leftRuns, List.replicate_succ, List.cons_append, moveLeft,
    List.drop_succ_cons, List.drop_zero, List.headD_cons, List.nil_append, List.append_assoc, Nat.add_assoc, hh] using hwhole

/-- From the same selected-block entry as the increment proof, a double-zero
left boundary suffices to continue through the return scan to raw state 68.
The explicit endpoint retains the entire tape zipper. -/
theorem increment_return_block (before : List Nat) (value : Nat) (rest : List Nat)
    (head : Int) (left tail : List Bool) :
    ∃ first values,
      rest.reverse ++ (value + 1) :: before.reverse = first :: values ∧
      rawSystem.Block
        ⟨9, head, ⟨(bank before).reverse ++ false :: false :: left,
          List.replicate (value + 1) true ++ false :: (bank rest ++ false :: tail)⟩⟩
        (UnaryIncrement.duration value rest + (first + 1 + (shiftTime values + 2)))
        ⟨68, head + ((value + 2 : Nat) : Int) + (shiftTime rest : Int) - 1 -
            ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2,
          moveLeft ⟨left, false :: false ::
            pushRuns values (List.replicate (first + 1) true ++ false :: tail)⟩ false⟩ [] := by
  have hn : rest.reverse ++ (value + 1) :: before.reverse ≠ [] := by
    simp
  cases he : rest.reverse ++ (value + 1) :: before.reverse with
  | nil => exact False.elim (hn he)
  | cons first values =>
    refine ⟨first, values, rfl, ?_⟩
    have hshift := increment_shifted_left before value rest left
    rw [he] at hshift
    have hfirst := UnaryIncrement.increment_block value rest head
      ((bank before).reverse ++ false :: false :: left) tail
    rw [hshift] at hfirst
    have hreturn := return_nonempty first values
      (head + ((value + 2 : Nat) : Int) + (shiftTime rest : Int) - 1) left tail
    exact hfirst.trans rawSystem hreturn

theorem pushRuns_bank (values : List Nat) (right : List Bool) :
    pushRuns values right = bank values.reverse ++ right := by
  induction values generalizing right with
  | nil => rfl
  | cons value rest ih =>
    simp [pushRuns, ih, List.reverse_cons, UnaryIncrement.bank_append, bank,
      List.replicate_succ, List.append_assoc]

theorem increment_return_word (before : List Nat) (value : Nat) (rest : List Nat)
    (first : Nat) (values : List Nat) (tail : List Bool)
    (he : rest.reverse ++ (value + 1) :: before.reverse = first :: values) :
    pushRuns values (List.replicate (first + 1) true ++ false :: tail) =
      bank (before ++ (value + 1) :: rest) ++ tail := by
  rw [pushRuns_bank]
  have h : values.reverse ++ [first] = before ++ (value + 1) :: rest := by
    have hr := congrArg List.reverse he
    simpa [List.reverse_append, List.reverse_cons, List.reverse_reverse, List.append_assoc] using hr.symm
  have hb : bank values.reverse ++ (List.replicate (first + 1) true ++ false :: tail) =
      bank (values.reverse ++ [first]) ++ tail := by
    simp [UnaryIncrement.bank_append, bank, List.replicate_succ, List.append_assoc]
  rw [hb, h]

/-- The increment-and-return composition lifts to both literal two-way tapes.
The source-register interpretation still requires the independently stated
entry and later control invariants. -/
theorem physical_increment_return (before : List Nat) (value : Nat) (rest : List Nat)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨9, head, ⟨(bank before).reverse ++ false :: false :: left,
        List.replicate (value + 1) true ++ false :: (bank rest ++ false :: tail)⟩⟩ c) :
    ∃ first values finish,
      rest.reverse ++ (value + 1) :: before.reverse = first :: values ∧
      (machineWordSystem raw rawLabels).Block c
        (UnaryIncrement.duration value rest + (first + 1 + (shiftTime values + 2))) finish [] ∧
      Related
        ⟨68, head + ((value + 2 : Nat) : Int) + (shiftTime rest : Int) - 1 -
            ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2,
          moveLeft ⟨left, false :: false ::
            (bank (before ++ (value + 1) :: rest) ++ tail)⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (UnaryIncrement.duration value rest + (first + 1 + (shiftTime values + 2)))
        (mapConfig finish) [] ∧
      0 < UnaryIncrement.duration value rest + (first + 1 + (shiftTime values + 2)) ∧
      UnaryCodec.decodeBank (before.length + 1 + rest.length)
        (bank (before ++ (value + 1) :: rest) ++ tail) =
        some (before ++ (value + 1) :: rest, tail) := by
  obtain ⟨first, values, he, hb⟩ := increment_return_block before value rest head left tail
  let duration := UnaryIncrement.duration value rest + (first + 1 + (shiftTime values + 2))
  have hs := advance_sound raw rawLabels hrel duration
  change Related (rawSystem.advance
      ⟨9, head, ⟨(bank before).reverse ++ false :: false :: left,
        List.replicate (value + 1) true ++ false :: (bank rest ++ false :: tail)⟩⟩ duration) _ ∧
    rawSystem.wordFrom
      ⟨9, head, ⟨(bank before).reverse ++ false :: false :: left,
        List.replicate (value + 1) true ++ false :: (bank rest ++ false :: tail)⟩⟩ duration = _ at hs
  rw [hb.endpoint, hb.output] at hs
  let finish := (machineWordSystem raw rawLabels).advance c duration
  have hp : (machineWordSystem raw rawLabels).Block c duration finish [] := ⟨rfl, hs.2.symm⟩
  have hw := increment_return_word before value rest first values tail he
  rw [hw] at hs
  refine ⟨first, values, finish, he, hp, hs.1, BootstrapScan.mapped_block hp, by omega, ?_⟩
  simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    UnaryCodec.decode_bank (before ++ (value + 1) :: rest) tail

/-- The untouched part of the tape and the decoded bank at the intermediate
state are the exact bank update of an increment, with no bound on its values. -/
theorem increment_intermediate_decodes (before : List Nat) (value : Nat) (rest : List Nat)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨9, head, ⟨(bank before).reverse ++ false :: false :: left,
        List.replicate (value + 1) true ++ false :: (bank rest ++ false :: tail)⟩⟩ c) :
    ∃ middle,
      (machineWordSystem raw rawLabels).Block c (UnaryIncrement.duration value rest) middle [] ∧
      Related
        ⟨35, head + ((value + 2 : Nat) : Int) + (shiftTime rest : Int) - 1,
          moveLeft ⟨shiftedLeft rest (true :: (List.replicate (value + 1) true ++
            ((bank before).reverse ++ false :: false :: left))), false :: tail⟩ false⟩ middle ∧
      UnaryIncrement.linear (moveLeft
        ⟨shiftedLeft rest (true :: (List.replicate (value + 1) true ++
          ((bank before).reverse ++ false :: false :: left))), false :: tail⟩ false) =
        (false :: false :: left).reverse ++ (bank (before ++ (value + 1) :: rest) ++ tail) ∧
      UnaryCodec.decodeBank (before.length + 1 + rest.length)
        (bank (before ++ (value + 1) :: rest) ++ tail) =
        some (before ++ (value + 1) :: rest, tail) := by
  obtain ⟨middle, hp, hr, _, hw, hd, _⟩ :=
    UnaryIncrement.physical_increment_in_bank before value rest head (false :: false :: left) tail c hrel
  exact ⟨middle, hp, hr, hw, hd⟩

/-- The nine-register operation and the raw-to-quotient physical execution
agree through the return to state 68, under the explicit boundary and entry
tape preconditions. -/
theorem physical_increment_return_nine
    (registers : RegisterMachine.Bank 9) (r : Fin 9) (reserve : List Nat)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨9, head, ⟨(bank (UnaryIncrementNine.before registers r)).reverse ++ false :: false :: left,
        List.replicate (registers r + 1) true ++ false ::
          (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail)⟩⟩ c) :
    ∃ first values finish,
      (UnaryIncrementNine.after registers r ++ reserve).reverse ++
          (registers r + 1) :: (UnaryIncrementNine.before registers r).reverse = first :: values ∧
      (machineWordSystem raw rawLabels).Block c
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2))) finish [] ∧
      Related
        ⟨68, head + ((registers r + 2 : Nat) : Int) +
            (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
            ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2,
          moveLeft ⟨left, false :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail)⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2))) (mapConfig finish) [] ∧
      0 < UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2)) ∧
      UnaryCodec.decodeBank (9 + reserve.length)
        (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve, tail) := by
  obtain ⟨first, values, finish, he, hp, hr, hq, ht, _⟩ :=
    physical_increment_return (UnaryIncrementNine.before registers r) (registers r)
      (UnaryIncrementNine.after registers r ++ reserve) head left tail c hrel
  have hvalues : UnaryIncrementNine.before registers r ++ (registers r + 1) ::
        (UnaryIncrementNine.after registers r ++ reserve) =
      UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve := by
    rw [UnaryIncrementNine.values_increment]
    simp [List.append_assoc]
  rw [hvalues] at hr
  refine ⟨first, values, finish, he, hp, hr, hq, ht, ?_⟩
  simpa only [List.length_append, UnaryNine.values_length] using
    UnaryCodec.decode_bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) tail

example : raw.table.row 36 false ≠ ⟨false, .left, 69, false⟩ := by decide
example : rawLabels.at 35 false = none ∧ rawLabels.at 36 false = none := by decide
example : mapState 68 = 67 := by decide
example : rawSystem.Block ⟨9, 0, ⟨[false, false], [true, false, false]⟩⟩ 7
    ⟨68, -3, ⟨[], [false, false, false, true, true, false]⟩⟩ [] := by
  constructor <;> decide
example : ¬ rawSystem.Block ⟨9, 0, ⟨[false, false], [true, false, false]⟩⟩ 6
    ⟨68, -3, ⟨[], [false, false, false, true, true, false]⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance ⟨9, 0, ⟨[false, false], [true, false, false]⟩⟩ 6 ≠
      ⟨68, -3, ⟨[], [false, false, false, true, true, false]⟩⟩ := by decide
  exact bad h.endpoint

end PASoundness.M236.UnaryReturn
