import PASoundness.M236UnaryCodec

/-!
The selected raw table's local unary increment path: state 9 extends one
unary run, states 33/34 shift the arbitrary remaining bank, and state 35 is
entered on the terminating zero. Selection and return-to-source control are
not assumed or proved here.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.UnaryIncrement
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

private theorem replicate_shift (n : Nat) (tail : List Bool) :
    List.replicate n true ++ (true :: tail) = true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- State 9 preserves an arbitrary finite run of ones and stops at its zero. -/
theorem scan_ones (count : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨9, head, ⟨left, List.replicate count true ++ false :: tail⟩⟩ count
      ⟨9, head + (count : Int), ⟨List.replicate count true ++ left, false :: tail⟩⟩ [] := by
  induction count generalizing head left with
  | zero =>
    simpa using WordEventSystem.Block.refl rawSystem ⟨9, head, ⟨left, false :: tail⟩⟩
  | succ count ih =>
    let t : Tape := ⟨left, List.replicate (count + 1) true ++ false :: tail⟩
    have row : raw.table.row 9 true = ⟨true, .right, 9, false⟩ := by decide
    have event : rawLabels.at 9 true = none := by decide
    have hstep : rawSystem.step ⟨9, head, t⟩ =
        (⟨9, head + 1, ⟨true :: left, List.replicate count true ++ false :: tail⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row, event,
        Move.apply, moveRight, t, List.replicate_succ]
    have hfirst := WordEventSystem.Block.single rawSystem hstep
    have hrest := ih (head + 1) (true :: left)
    have hwhole := hfirst.trans rawSystem hrest
    have ht : 1 + count = count + 1 := by omega
    have hh : head + 1 + (count : Int) = head + ((count + 1 : Nat) : Int) := by omega
    simpa only [t, List.nil_append, ht, hh, List.replicate_succ,
      List.cons_append, replicate_shift] using hwhole

/-- The leading delimiter of every shifted suffix is exactly the separator
needed after the incremented block; all suffix values remain in order. -/
theorem shifted_sentinel (values : List Nat) (tail : List Bool) :
    shiftedWord values ++ false :: tail = false :: (bank values ++ tail) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [shiftedWord, bank, List.cons_append, List.append_assoc, ih,
      List.replicate_succ]

/-- The table writes an extra one at the selected block's separator and
enters the already verified suffix-shift state. -/
theorem extend_selected (value : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block
      ⟨9, head, ⟨left, List.replicate (value + 1) true ++ false :: tail⟩⟩
      (value + 2)
      ⟨33, head + ((value + 2 : Nat) : Int),
        ⟨true :: (List.replicate (value + 1) true ++ left), tail⟩⟩ [] := by
  have hscan := scan_ones (value + 1) head left tail
  have row : raw.table.row 9 false = ⟨true, .right, 33, false⟩ := by decide
  have event : rawLabels.at 9 false = none := by decide
  have hstep : rawSystem.step ⟨9, head + ((value + 1 : Nat) : Int),
      ⟨List.replicate (value + 1) true ++ left, false :: tail⟩⟩ =
      (⟨33, head + ((value + 1 : Nat) : Int) + 1,
        ⟨true :: (List.replicate (value + 1) true ++ left), tail⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row, event,
      Move.apply, moveRight]
  have hwhole := hscan.trans rawSystem (WordEventSystem.Block.single rawSystem hstep)
  have ht : (value + 1) + 1 = value + 2 := by omega
  have hh : head + ((value + 1 : Nat) : Int) + 1 = head + ((value + 2 : Nat) : Int) := by omega
  simpa only [List.nil_append, ht, hh] using hwhole

def duration (value : Nat) (rest : List Nat) : Nat := value + 2 + shiftTime rest + 1

/-- Actual table execution from state 9 through suffix shift and stop. -/
theorem increment_block (value : Nat) (rest : List Nat) (head : Int)
    (left tail : List Bool) :
    rawSystem.Block
      ⟨9, head, ⟨left, List.replicate (value + 1) true ++ false ::
        (bank rest ++ false :: tail)⟩⟩
      (duration value rest)
      ⟨35, head + ((value + 2 : Nat) : Int) + (shiftTime rest : Int) - 1,
        moveLeft ⟨shiftedLeft rest (true :: (List.replicate (value + 1) true ++ left)),
          false :: tail⟩ false⟩ [] := by
  have hfirst := extend_selected value head left (bank rest ++ false :: tail)
  have hrest := shift_bank_stop rest (head + ((value + 2 : Nat) : Int))
    (true :: (List.replicate (value + 1) true ++ left)) tail
  have hwhole := hfirst.trans rawSystem hrest
  simpa only [duration, List.nil_append, Nat.add_assoc] using hwhole

/-- A finite zipper read in physical left-to-right order. -/
def linear (t : Tape) : List Bool := t.left.reverse ++ t.right

private theorem moveLeft_zero_linear (left tail : List Bool) (h : left ≠ []) :
    linear (moveLeft ⟨left, false :: tail⟩ false) = left.reverse ++ false :: tail := by
  cases left with
  | nil => contradiction
  | cons b left => simp [linear, moveLeft, List.reverse_cons, List.append_assoc]

/-- After the physical increment, the finite tape word is exactly the old
left context followed by the incremented block and the unchanged bank. The
first trailing blank is consumed to make space. -/
theorem incremented_linear (value : Nat) (rest : List Nat) (left tail : List Bool) :
    linear (moveLeft
      ⟨shiftedLeft rest (true :: (List.replicate (value + 1) true ++ left)),
        false :: tail⟩ false) =
      left.reverse ++ (bank ((value + 1) :: rest) ++ tail) := by
  have hne : shiftedLeft rest (true :: (List.replicate (value + 1) true ++ left)) ≠ [] := by
    rw [shiftedLeft_eq]
    simp
  rw [moveLeft_zero_linear _ _ hne, shiftedLeft_eq]
  simp only [List.reverse_append, List.reverse_reverse, List.reverse_cons,
    List.reverse_replicate, List.append_assoc]
  rw [shifted_sentinel]
  simp only [bank, List.cons_append, List.append_assoc]
  rw [replicate_shift]
  simp only [List.nil_append]

theorem bank_append (before suffix : List Nat) :
    bank (before ++ suffix) = bank before ++ bank suffix := by
  induction before with
  | nil => rfl
  | cons value before ih => simp [bank, ih, List.append_assoc]

/-- Encoded values to the left of the selected block are preserved as well
as all suffix values. -/
theorem incremented_whole_bank (before : List Nat) (value : Nat) (rest : List Nat)
    (left tail : List Bool) :
    linear (moveLeft
      ⟨shiftedLeft rest (true :: (List.replicate (value + 1) true ++
          ((bank before).reverse ++ left))), false :: tail⟩ false) =
      left.reverse ++ (bank (before ++ (value + 1) :: rest) ++ tail) := by
  rw [incremented_linear, bank_append]
  simp [List.reverse_append, List.append_assoc]

/-- A positive, silent physical increment block for the actual raw table and
its selected quotient. The exact finite tape word decodes to the incremented
value followed by the unchanged suffix values. -/
theorem physical_increment (value : Nat) (rest : List Nat) (head : Int)
    (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨9, head, ⟨left, List.replicate (value + 1) true ++ false ::
        (bank rest ++ false :: tail)⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (duration value rest) finish [] ∧
      Related
        ⟨35, head + ((value + 2 : Nat) : Int) + (shiftTime rest : Int) - 1,
          moveLeft ⟨shiftedLeft rest (true :: (List.replicate (value + 1) true ++ left)),
            false :: tail⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (duration value rest)
        (mapConfig finish) [] ∧
      linear (moveLeft
        ⟨shiftedLeft rest (true :: (List.replicate (value + 1) true ++ left)),
          false :: tail⟩ false) =
        left.reverse ++ (bank ((value + 1) :: rest) ++ tail) ∧
      UnaryCodec.decodeBank (rest.length + 1) (bank ((value + 1) :: rest) ++ tail) =
        some ((value + 1) :: rest, tail) ∧
      0 < duration value rest := by
  have hb := increment_block value rest head left tail
  have hs := advance_sound raw rawLabels hrel (duration value rest)
  change Related (rawSystem.advance
      ⟨9, head, ⟨left, List.replicate (value + 1) true ++ false ::
        (bank rest ++ false :: tail)⟩⟩ (duration value rest)) _ ∧
    rawSystem.wordFrom
      ⟨9, head, ⟨left, List.replicate (value + 1) true ++ false ::
        (bank rest ++ false :: tail)⟩⟩ (duration value rest) = _ at hs
  rw [hb.endpoint, hb.output] at hs
  let finish := (machineWordSystem raw rawLabels).advance c (duration value rest)
  have hp : (machineWordSystem raw rawLabels).Block c (duration value rest) finish [] :=
    ⟨rfl, hs.2.symm⟩
  refine ⟨finish, hp, hs.1, BootstrapScan.mapped_block hp,
    incremented_linear value rest left tail, ?_, ?_⟩
  · simpa using UnaryCodec.decode_bank ((value + 1) :: rest) tail
  · simp only [duration]
    omega

/-- The local physical increment preserves every encoded prefix and suffix
value, with the final separator supplied by the trailing blank. -/
theorem physical_increment_in_bank (before : List Nat) (value : Nat) (rest : List Nat)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨9, head, ⟨(bank before).reverse ++ left, List.replicate (value + 1) true ++ false ::
        (bank rest ++ false :: tail)⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (duration value rest) finish [] ∧
      Related
        ⟨35, head + ((value + 2 : Nat) : Int) + (shiftTime rest : Int) - 1,
          moveLeft ⟨shiftedLeft rest (true :: (List.replicate (value + 1) true ++
            ((bank before).reverse ++ left))), false :: tail⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (duration value rest)
        (mapConfig finish) [] ∧
      linear (moveLeft
        ⟨shiftedLeft rest (true :: (List.replicate (value + 1) true ++
          ((bank before).reverse ++ left))), false :: tail⟩ false) =
        left.reverse ++ (bank (before ++ (value + 1) :: rest) ++ tail) ∧
      UnaryCodec.decodeBank (before.length + 1 + rest.length)
        (bank (before ++ (value + 1) :: rest) ++ tail) =
        some (before ++ (value + 1) :: rest, tail) ∧
      0 < duration value rest := by
  obtain ⟨finish, hp, hr, hq, _, _, hpos⟩ :=
    physical_increment value rest head ((bank before).reverse ++ left) tail c hrel
  refine ⟨finish, hp, hr, hq, incremented_whole_bank before value rest left tail, ?_, hpos⟩
  simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    UnaryCodec.decode_bank (before ++ (value + 1) :: rest) tail

example : raw.table.row 9 false ≠ ⟨true, .left, 33, false⟩ := by decide
example : rawLabels.at 9 false = none ∧ rawLabels.at 9 true = none := by decide
example : mapState 9 = 9 := by decide
example : mapState 35 = 34 := by decide
example : rawSystem.Block ⟨9, 0, ⟨[], [true, false, false]⟩⟩ 3
    ⟨35, 1, ⟨[true], [true, false]⟩⟩ [] := by
  constructor <;> decide
example : ¬ rawSystem.Block ⟨9, 0, ⟨[], [true, false, false]⟩⟩ 2
    ⟨35, 1, ⟨[true], [true, false]⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance ⟨9, 0, ⟨[], [true, false, false]⟩⟩ 2 ≠
      ⟨35, 1, ⟨[true], [true, false]⟩⟩ := by decide
  exact bad h.endpoint

end PASoundness.M236.UnaryIncrement
