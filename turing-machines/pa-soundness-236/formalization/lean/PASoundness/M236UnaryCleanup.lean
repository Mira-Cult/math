import PASoundness.M236UnaryReturn

/-! The literal state-68 cleanup and state-39/40 control scan. This proves
only table behavior; the source-level meaning of the cleared cells and state 1
is not assumed. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.UnaryCleanup
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

private theorem replicate_shift (b : Bool) (n : Nat) (tail : List Bool) :
    List.replicate n b ++ (b :: tail) = b :: (List.replicate n b ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- Raw state 68 erases an arbitrary finite run while moving left. -/
theorem erase_left (count : Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block ⟨68, head, ⟨List.replicate count true ++ left, true :: right⟩⟩ count
      ⟨68, head - (count : Int), ⟨left, true :: (List.replicate count false ++ right)⟩⟩ [] := by
  induction count generalizing head right with
  | zero => simpa using WordEventSystem.Block.refl rawSystem ⟨68, head, ⟨left, true :: right⟩⟩
  | succ count ih =>
    have row : raw.table.row 68 true = ⟨false, .left, 68, false⟩ := by decide
    have ev : rawLabels.at 68 true = none := by decide
    have hs : rawSystem.step
        ⟨68, head, ⟨List.replicate (count + 1) true ++ left, true :: right⟩⟩ =
        (⟨68, head - 1, ⟨List.replicate count true ++ left, true :: false :: right⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row, ev,
        Move.apply, moveLeft, List.replicate_succ]
    have hb := (WordEventSystem.Block.single rawSystem hs).trans rawSystem
      (ih (head - 1) (false :: right))
    have hh : head - 1 - (count : Int) = head - ((count + 1 : Nat) : Int) := by omega
    simpa only [List.nil_append, hh, Nat.add_comm 1 count, List.replicate_succ,
      List.cons_append, replicate_shift] using hb

/-- State 39 moves right over any finite run of zeros. -/
theorem scan_right_zeros (count : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨39, head, ⟨left, List.replicate count false ++ true :: tail⟩⟩ count
      ⟨39, head + (count : Int), ⟨List.replicate count false ++ left, true :: tail⟩⟩ [] := by
  induction count generalizing head left with
  | zero => simpa using WordEventSystem.Block.refl rawSystem ⟨39, head, ⟨left, true :: tail⟩⟩
  | succ count ih =>
    have row : raw.table.row 39 false = ⟨false, .right, 39, false⟩ := by decide
    have ev : rawLabels.at 39 false = none := by decide
    have hs : rawSystem.step
        ⟨39, head, ⟨left, List.replicate (count + 1) false ++ true :: tail⟩⟩ =
        (⟨39, head + 1, ⟨false :: left, List.replicate count false ++ true :: tail⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row, ev,
        Move.apply, moveRight, List.replicate_succ]
    have hb := (WordEventSystem.Block.single rawSystem hs).trans rawSystem
      (ih (head + 1) (false :: left))
    have hh : head + 1 + (count : Int) = head + ((count + 1 : Nat) : Int) := by omega
    simpa only [List.nil_append, hh, Nat.add_comm 1 count, List.replicate_succ,
      List.cons_append, replicate_shift] using hb

/-- State 40 erases every one in an arbitrary run while moving right. -/
theorem erase_right (count : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨40, head, ⟨left, List.replicate count true ++ false :: tail⟩⟩ count
      ⟨40, head + (count : Int), ⟨List.replicate count false ++ left, false :: tail⟩⟩ [] := by
  induction count generalizing head left with
  | zero => simpa using WordEventSystem.Block.refl rawSystem ⟨40, head, ⟨left, false :: tail⟩⟩
  | succ count ih =>
    have row : raw.table.row 40 true = ⟨false, .right, 40, false⟩ := by decide
    have ev : rawLabels.at 40 true = none := by decide
    have hs : rawSystem.step
        ⟨40, head, ⟨left, List.replicate (count + 1) true ++ false :: tail⟩⟩ =
        (⟨40, head + 1, ⟨false :: left, List.replicate count true ++ false :: tail⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row, ev,
        Move.apply, moveRight, List.replicate_succ]
    have hb := (WordEventSystem.Block.single rawSystem hs).trans rawSystem
      (ih (head + 1) (false :: left))
    have hh : head + 1 + (count : Int) = head + ((count + 1 : Nat) : Int) := by omega
    simpa only [List.nil_append, hh, Nat.add_comm 1 count, List.replicate_succ,
      List.cons_append, replicate_shift] using hb

/-- Clean up the run to the left of the increment boundary, write its
terminating zero to one, and enter state 39. -/
theorem erase_left_stop (count : Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block
      ⟨68, head, moveLeft ⟨List.replicate count true ++ false :: left, false :: right⟩ false⟩
      (count + 1)
      ⟨39, head - (count : Int) + 1,
        ⟨true :: left, List.replicate count false ++ false :: right⟩⟩ [] := by
  have row0 : raw.table.row 68 false = ⟨true, .right, 39, false⟩ := by decide
  have ev0 : rawLabels.at 68 false = none := by decide
  cases count with
  | zero =>
    have hs : rawSystem.step ⟨68, head, ⟨left, false :: false :: right⟩⟩ =
        (⟨39, head + 1, ⟨true :: left, false :: right⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row0, ev0,
        Move.apply, moveRight]
    simpa [moveLeft] using WordEventSystem.Block.single rawSystem hs
  | succ count =>
    have hscan := erase_left count head (false :: left) (false :: right)
    have row1 : raw.table.row 68 true = ⟨false, .left, 68, false⟩ := by decide
    have ev1 : rawLabels.at 68 true = none := by decide
    have hs1 : rawSystem.step
        ⟨68, head - (count : Int),
          ⟨false :: left, true :: (List.replicate count false ++ false :: right)⟩⟩ =
        (⟨68, head - (count : Int) - 1,
          ⟨left, false :: false :: (List.replicate count false ++ false :: right)⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row1, ev1,
        Move.apply, moveLeft]
    have hs0 : rawSystem.step
        ⟨68, head - (count : Int) - 1,
          ⟨left, false :: false :: (List.replicate count false ++ false :: right)⟩⟩ =
        (⟨39, head - (count : Int),
          ⟨true :: left, false :: (List.replicate count false ++ false :: right)⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row0, ev0,
        Move.apply, moveRight]
    have hb := (hscan.trans rawSystem (WordEventSystem.Block.single rawSystem hs1)).trans rawSystem
      (WordEventSystem.Block.single rawSystem hs0)
    have hh : head - (count : Int) = head - (((count + 1) : Nat) : Int) + 1 := by omega
    simpa only [moveLeft, List.replicate_succ, List.cons_append, List.drop_succ_cons,
      List.drop_zero, List.headD_cons, List.nil_append, Nat.add_assoc, hh] using hb

/-- State 39 seeks the first one; states 39/40 then erase the entire run
and state 40 enters raw state 1 on its terminating zero. -/
theorem seek_and_erase (count value : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block
      ⟨39, head, ⟨left, List.replicate count false ++ true ::
        (List.replicate value true ++ false :: tail)⟩⟩
      (count + value + 2)
      ⟨1, head + (count : Int) + (value : Int),
        moveLeft ⟨List.replicate value false ++ false ::
          (List.replicate count false ++ left), false :: tail⟩ false⟩ [] := by
  have hscan := scan_right_zeros count head left (List.replicate value true ++ false :: tail)
  have row0 : raw.table.row 39 true = ⟨false, .right, 40, false⟩ := by decide
  have ev0 : rawLabels.at 39 true = none := by decide
  have hs0 : rawSystem.step
      ⟨39, head + (count : Int),
        ⟨List.replicate count false ++ left, true :: (List.replicate value true ++ false :: tail)⟩⟩ =
      (⟨40, head + (count : Int) + 1,
        ⟨false :: (List.replicate count false ++ left), List.replicate value true ++ false :: tail⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row0, ev0,
      Move.apply, moveRight]
  have herase := erase_right value (head + (count : Int) + 1)
    (false :: (List.replicate count false ++ left)) tail
  have row1 : raw.table.row 40 false = ⟨false, .left, 1, false⟩ := by decide
  have ev1 : rawLabels.at 40 false = none := by decide
  have hs1 : rawSystem.step
      ⟨40, head + (count : Int) + 1 + (value : Int),
        ⟨List.replicate value false ++ false :: (List.replicate count false ++ left), false :: tail⟩⟩ =
      (⟨1, head + (count : Int) + (value : Int),
        moveLeft ⟨List.replicate value false ++ false ::
          (List.replicate count false ++ left), false :: tail⟩ false⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row1, ev1,
      Move.apply]
    omega
  have hb := ((hscan.trans rawSystem (WordEventSystem.Block.single rawSystem hs0)).trans rawSystem
    herase).trans rawSystem (WordEventSystem.Block.single rawSystem hs1)
  have ht : count + 1 + value + 1 = count + value + 2 := by omega
  simpa only [List.nil_append, ht] using hb

/-- From the return boundary, clear a finite left scratch run, then erase
the first unary bank run before entering raw state 1. The rest of the bank
and all outer tape data remain explicitly represented. -/
theorem cleanup_block (scratch value : Nat) (values : List Nat) (head : Int)
    (left tail : List Bool) :
    rawSystem.Block
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: false :: (bank (value :: values) ++ tail)⟩ false⟩
      (2 * scratch + value + 5)
      ⟨1, head + (value : Int) + 3,
        moveLeft ⟨List.replicate value false ++ false ::
          (List.replicate (scratch + 2) false ++ true :: left),
          false :: (bank values ++ tail)⟩ false⟩ [] := by
  have hraw := erase_left_stop scratch head left (false :: (bank (value :: values) ++ tail))
  have hfirst : rawSystem.Block
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: false :: (bank (value :: values) ++ tail)⟩ false⟩
      (scratch + 1)
      ⟨39, head - (scratch : Int) + 1,
        ⟨true :: left, List.replicate (scratch + 2) false ++ true ::
          (List.replicate value true ++ false :: (bank values ++ tail))⟩⟩ [] := by
    simpa [bank, List.replicate_succ, List.append_assoc, replicate_shift] using hraw
  have hseek := seek_and_erase (scratch + 2) value (head - (scratch : Int) + 1)
    (true :: left) (bank values ++ tail)
  have hb := hfirst.trans rawSystem hseek
  have ht : scratch + 1 + ((scratch + 2) + value + 2) = 2 * scratch + value + 5 := by omega
  have hh : head - (scratch : Int) + 1 + ((scratch + 2 : Nat) : Int) + (value : Int) =
      head + (value : Int) + 3 := by omega
  simpa only [List.nil_append, ht, hh] using hb

/-- The cleanup block refines both full two-way-tape machines, with the
same exact time and no emitted event. -/
theorem physical_cleanup (scratch value : Nat) (values : List Nat) (head : Int)
    (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: false :: (bank (value :: values) ++ tail)⟩ false⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (2 * scratch + value + 5) finish [] ∧
      Related
        ⟨1, head + (value : Int) + 3,
          moveLeft ⟨List.replicate value false ++ false ::
            (List.replicate (scratch + 2) false ++ true :: left),
            false :: (bank values ++ tail)⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (2 * scratch + value + 5) (mapConfig finish) [] ∧
      0 < 2 * scratch + value + 5 := by
  have hb := cleanup_block scratch value values head left tail
  have hs := advance_sound raw rawLabels hrel (2 * scratch + value + 5)
  change Related (rawSystem.advance
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: false :: (bank (value :: values) ++ tail)⟩ false⟩
      (2 * scratch + value + 5)) _ ∧
    rawSystem.wordFrom
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: false :: (bank (value :: values) ++ tail)⟩ false⟩
      (2 * scratch + value + 5) = _ at hs
  rw [hb.endpoint, hb.output] at hs
  let finish := (machineWordSystem raw rawLabels).advance c (2 * scratch + value + 5)
  have hp : (machineWordSystem raw rawLabels).Block c (2 * scratch + value + 5) finish [] :=
    ⟨rfl, hs.2.symm⟩
  exact ⟨finish, hp, hs.1, BootstrapScan.mapped_block hp, by omega⟩

/-- Compose the literal increment, left return, and cleanup through state 1.
The first updated bank value is intentionally erased during the final scan;
the theorem does not call that value restored. -/
theorem physical_increment_cleanup
    (before : List Nat) (value : Nat) (rest : List Nat)
    (control : Nat) (others : List Nat)
    (hbank : before ++ (value + 1) :: rest = control :: others)
    (scratch : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨9, head, ⟨(bank before).reverse ++ false :: false ::
          (List.replicate scratch true ++ false :: left),
        List.replicate (value + 1) true ++ false :: (bank rest ++ false :: tail)⟩⟩ c) :
    ∃ first values middle finish,
      rest.reverse ++ (value + 1) :: before.reverse = first :: values ∧
      (machineWordSystem raw rawLabels).Block c
        (UnaryIncrement.duration value rest + (first + 1 + (shiftTime values + 2))) middle [] ∧
      Related
        ⟨68, head + ((value + 2 : Nat) : Int) + (shiftTime rest : Int) - 1 -
            ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2,
          moveLeft ⟨List.replicate scratch true ++ false :: left,
            false :: false :: (bank (control :: others) ++ tail)⟩ false⟩ middle ∧
      (machineWordSystem raw rawLabels).Block c
        (UnaryIncrement.duration value rest + (first + 1 + (shiftTime values + 2)) +
          (2 * scratch + control + 5)) finish [] ∧
      Related
        ⟨1, head + ((value + 2 : Nat) : Int) + (shiftTime rest : Int) - 1 -
            ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2 + (control : Int) + 3,
          moveLeft ⟨List.replicate control false ++ false ::
            (List.replicate (scratch + 2) false ++ true :: left),
            false :: (bank others ++ tail)⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (UnaryIncrement.duration value rest + (first + 1 + (shiftTime values + 2)) +
          (2 * scratch + control + 5)) (mapConfig finish) [] ∧
      0 < UnaryIncrement.duration value rest + (first + 1 + (shiftTime values + 2)) +
        (2 * scratch + control + 5) := by
  obtain ⟨first, values, middle, he, hp, hr, hq, ht, _⟩ :=
    UnaryReturn.physical_increment_return before value rest head
      (List.replicate scratch true ++ false :: left) tail c hrel
  rw [hbank] at hr
  obtain ⟨finish, hp', hr', hq', _⟩ := physical_cleanup scratch control others
    (head + ((value + 2 : Nat) : Int) + (shiftTime rest : Int) - 1 -
      ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2) left tail middle hr
  refine ⟨first, values, middle, finish, he, hp, hr, ?_, hr', ?_, by omega⟩
  · simpa using hp.trans (machineWordSystem raw rawLabels) hp'
  · simpa using hq.trans (machineWordSystem machine machineLabels) hq'

/-- Nine-register instance through raw state 1. The split identifies the
updated bank before cleanup; the first encoded run is erased by cleanup. -/
theorem physical_increment_cleanup_nine
    (registers : RegisterMachine.Bank 9) (r : Fin 9) (reserve : List Nat)
    (scratch : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨9, head, ⟨(bank (UnaryIncrementNine.before registers r)).reverse ++ false :: false ::
          (List.replicate scratch true ++ false :: left),
        List.replicate (registers r + 1) true ++ false ::
          (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail)⟩⟩ c) :
    ∃ first values control others middle finish,
      (UnaryIncrementNine.after registers r ++ reserve).reverse ++
        (registers r + 1) :: (UnaryIncrementNine.before registers r).reverse = first :: values ∧
      UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve = control :: others ∧
      (machineWordSystem raw rawLabels).Block c
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2))) middle [] ∧
      Related
        ⟨68, head + ((registers r + 2 : Nat) : Int) +
            (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
            ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2,
          moveLeft ⟨List.replicate scratch true ++ false :: left,
            false :: false :: (bank (control :: others) ++ tail)⟩ false⟩ middle ∧
      (machineWordSystem raw rawLabels).Block c
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2)) + (2 * scratch + control + 5)) finish [] ∧
      Related
        ⟨1, head + ((registers r + 2 : Nat) : Int) +
            (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
            ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2 + (control : Int) + 3,
          moveLeft ⟨List.replicate control false ++ false ::
            (List.replicate (scratch + 2) false ++ true :: left),
            false :: (bank others ++ tail)⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2)) + (2 * scratch + control + 5))
        (mapConfig finish) [] ∧
      0 < UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
          (first + 1 + (shiftTime values + 2)) + (2 * scratch + control + 5) := by
  have hnonempty : UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve ≠ [] := by
    intro h
    have hl := congrArg List.length h
    simp only [List.length_append, UnaryNine.values_length, List.length_nil] at hl
    omega
  cases hbank : UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve with
  | nil => exact False.elim (hnonempty hbank)
  | cons control others =>
    have hvalues : UnaryIncrementNine.before registers r ++ (registers r + 1) ::
        (UnaryIncrementNine.after registers r ++ reserve) = control :: others := by
      rw [← hbank, UnaryIncrementNine.values_increment]
      simp [List.append_assoc]
    obtain ⟨first, values, middle, finish, he, hp, hr, hp', hr', hq, ht⟩ :=
      physical_increment_cleanup (UnaryIncrementNine.before registers r) (registers r)
        (UnaryIncrementNine.after registers r ++ reserve) control others hvalues scratch head left tail c hrel
    exact ⟨first, values, control, others, middle, finish, he, rfl, hp, hr, hp', hr', hq, ht⟩

example : raw.table.row 68 true ≠ ⟨true, .left, 68, false⟩ := by decide
example : raw.table.row 39 true ≠ ⟨true, .right, 40, false⟩ := by decide
example : rawLabels.at 68 false = none ∧ rawLabels.at 39 true = none ∧
    rawLabels.at 40 false = none := by decide
example : mapState 68 = 67 ∧ mapState 1 = 1 := by decide
example : rawSystem.Block ⟨9, 0, ⟨[false, false, false], [true, false, false]⟩⟩ 13
    ⟨1, 1, ⟨[false, false, false, true], [false, false]⟩⟩ [] := by
  constructor <;> decide
example : ¬ rawSystem.Block ⟨9, 0, ⟨[false, false, false], [true, false, false]⟩⟩ 12
    ⟨1, 1, ⟨[false, false, false, true], [false, false]⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance ⟨9, 0, ⟨[false, false, false], [true, false, false]⟩⟩ 12 ≠
      ⟨1, 1, ⟨[false, false, false, true], [false, false]⟩⟩ := by decide
  exact bad h.endpoint

end PASoundness.M236.UnaryCleanup
