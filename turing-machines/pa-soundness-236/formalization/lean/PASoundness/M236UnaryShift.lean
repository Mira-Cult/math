import PASoundness.M236BulkSweep

/-!
Literal unary-bank shift rows of the selected raw machine. All tape lists are
nearest-head first and their omitted backgrounds are zero. These blocks are
unbounded in segment length and retain the exact tape, time and event word.
They do not yet establish which source operation reaches their preconditions.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.UnaryShift

open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.GenericSweep

def rawSystem := FiniteTape.system raw rawLabels

private theorem replicate_shift (b : Bool) (n : Nat) (tail : List Bool) :
    List.replicate n b ++ (b :: tail) = b :: (List.replicate n b ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- State 34 scans an arbitrary finite run of ones to the right without
changing it, stopping on the following zero. -/
theorem scan_ones (count : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨34, head, ⟨left, List.replicate count true ++ false :: tail⟩⟩ count
      ⟨34, head + (count : Int), ⟨List.replicate count true ++ left, false :: tail⟩⟩ [] := by
  induction count generalizing head left with
  | zero =>
    simpa using WordEventSystem.Block.refl rawSystem ⟨34, head, ⟨left, false :: tail⟩⟩
  | succ count ih =>
    let t : Tape := ⟨left, List.replicate (count + 1) true ++ false :: tail⟩
    have row : raw.table.row 34 true = ⟨true, .right, 34, false⟩ := by decide
    have event : rawLabels.at 34 true = none := by decide
    have hstep : rawSystem.step ⟨34, head, t⟩ =
        (⟨34, head + 1, ⟨true :: left, List.replicate count true ++ false :: tail⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row, event,
        Move.apply, moveRight, t, List.replicate_succ]
    have hfirst := WordEventSystem.Block.single rawSystem hstep
    have hrest := ih (head + 1) (true :: left)
    have hwhole := hfirst.trans rawSystem hrest
    have ht : 1 + count = count + 1 := by omega
    have hh : head + 1 + (count : Int) = head + ((count + 1 : Nat) : Int) := by omega
    simpa only [t, List.nil_append, ht, hh, List.replicate_succ,
      List.cons_append, replicate_shift] using hwhole

/-- One nonempty unary bank block `1^(value+1) 0` is transformed to
`0 1^(value+1)`, with the scan ready at the next block. -/
theorem shift_block (value : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block
      ⟨33, head, ⟨left, true :: (List.replicate value true ++ false :: tail)⟩⟩
      (value + 2)
      ⟨33, head + ((value + 2 : Nat) : Int),
        ⟨true :: (List.replicate value true ++ false :: left), tail⟩⟩ [] := by
  let t : Tape := ⟨left, true :: (List.replicate value true ++ false :: tail)⟩
  have row0 : raw.table.row 33 true = ⟨false, .right, 34, false⟩ := by decide
  have event0 : rawLabels.at 33 true = none := by decide
  have hstep0 : rawSystem.step ⟨33, head, t⟩ =
      (⟨34, head + 1, ⟨false :: left, List.replicate value true ++ false :: tail⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row0, event0,
      Move.apply, moveRight, t]
  have hfirst := WordEventSystem.Block.single rawSystem hstep0
  have hscan := scan_ones value (head + 1) (false :: left) tail
  let tend : Tape := ⟨List.replicate value true ++ false :: left, false :: tail⟩
  have row1 : raw.table.row 34 false = ⟨true, .right, 33, false⟩ := by decide
  have event1 : rawLabels.at 34 false = none := by decide
  have hstep1 : rawSystem.step ⟨34, head + 1 + (value : Int), tend⟩ =
      (⟨33, head + 1 + (value : Int) + 1,
        ⟨true :: (List.replicate value true ++ false :: left), tail⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row1, event1,
      Move.apply, moveRight, tend]
  have hlast := WordEventSystem.Block.single rawSystem hstep1
  have hwhole := (hfirst.trans rawSystem hscan).trans rawSystem hlast
  have ht : 1 + value + 1 = value + 2 := by omega
  have hh : head + 1 + (value : Int) + 1 = head + ((value + 2 : Nat) : Int) := by omega
  simpa only [List.nil_append, ht, hh] using hwhole

/-- A finite unary bank: value `v` is a run of `v + 1` ones followed by
a zero. The list and all values are arbitrary and have no global bound. -/
def bank : List Nat → List Bool
  | [] => []
  | value :: rest => true :: (List.replicate value true ++ false :: bank rest)

theorem bank_zeros (count : Nat) :
    bank (List.replicate count 0) = BulkSweep.pairs true false count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [bank, BulkSweep.pairs, List.replicate_succ, ih]

/-- Nearest-left-first result after shifting every encoded block. -/
def shiftedLeft : List Nat → List Bool → List Bool
  | [], left => left
  | value :: rest, left =>
      shiftedLeft rest (true :: (List.replicate value true ++ false :: left))

/-- The same result in left-to-right tape order: each bank block's zero is
moved before, rather than after, its run of ones. -/
def shiftedWord : List Nat → List Bool
  | [] => []
  | value :: rest => false :: (List.replicate (value + 1) true ++ shiftedWord rest)

theorem shiftedLeft_eq (values : List Nat) (left : List Bool) :
    shiftedLeft values left = (shiftedWord values).reverse ++ left := by
  induction values generalizing left with
  | nil => simp [shiftedLeft, shiftedWord]
  | cons value rest ih =>
    simp only [shiftedLeft, shiftedWord, ih, List.reverse_cons, List.reverse_append,
      List.reverse_replicate, List.replicate_succ, List.cons_append, List.append_assoc,
      List.nil_append, replicate_shift]

def shiftTime : List Nat → Nat
  | [] => 0
  | value :: rest => value + 2 + shiftTime rest

theorem shiftTime_eq_bank_length (values : List Nat) :
    shiftTime values = (bank values).length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [shiftTime, bank, List.length_cons, List.length_append,
      List.length_replicate, ih]
    omega

theorem shiftedWord_length (values : List Nat) :
    (shiftedWord values).length = (bank values).length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [shiftedWord, bank, List.length_cons, List.length_append,
      List.length_replicate, ih]
    omega

/-- All blocks are shifted by the actual table, for any finite bank and any
unchanged suffix. Empty banks take zero time; every nonempty bank progresses. -/
theorem shift_bank (values : List Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨33, head, ⟨left, bank values ++ tail⟩⟩ (shiftTime values)
      ⟨33, head + (shiftTime values : Int), ⟨shiftedLeft values left, tail⟩⟩ [] ∧
        (values ≠ [] → 0 < shiftTime values) := by
  induction values generalizing head left with
  | nil =>
    constructor
    · simpa [bank, shiftTime, shiftedLeft] using
        WordEventSystem.Block.refl rawSystem ⟨33, head, ⟨left, tail⟩⟩
    · simp
  | cons value rest ih =>
    have hfirst := shift_block value head left (bank rest ++ tail)
    have hrest := ih (head + ((value + 2 : Nat) : Int))
      (true :: (List.replicate value true ++ false :: left))
    have hwhole := hfirst.trans rawSystem hrest.1
    have hh : head + ((value + 2 : Nat) : Int) + (shiftTime rest : Int) =
        head + ((value + 2 + shiftTime rest : Nat) : Int) := by omega
    constructor
    · simpa only [bank, shiftedLeft, shiftTime, List.nil_append, List.cons_append,
        List.append_assoc, hh] using hwhole
    · intro _
      simp only [shiftTime]
      omega

/-- After the final bank block, the following zero takes the literal
state-33 stop row to state 35. The full zipper still records the suffix. -/
theorem shift_bank_stop (values : List Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨33, head, ⟨left, bank values ++ false :: tail⟩⟩ (shiftTime values + 1)
      ⟨35, head + (shiftTime values : Int) - 1,
        moveLeft ⟨shiftedLeft values left, false :: tail⟩ false⟩ [] := by
  have hscan := (shift_bank values head left (false :: tail)).1
  have row : raw.table.row 33 false = ⟨false, .left, 35, false⟩ := by decide
  have event : rawLabels.at 33 false = none := by decide
  have hstep : rawSystem.step ⟨33, head + (shiftTime values : Int),
      ⟨shiftedLeft values left, false :: tail⟩⟩ =
      (⟨35, head + (shiftTime values : Int) - 1,
        moveLeft ⟨shiftedLeft values left, false :: tail⟩ false⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, row, event, Move.apply]
  simpa using hscan.trans rawSystem (WordEventSystem.Block.single rawSystem hstep)

/-- The finite zipper block refines both actual two-way-tape machines,
including the selected quotient, without changing the event word. -/
theorem physical_and_quotient (values : List Nat) (head : Int) (left tail : List Bool)
    (c : Config 237)
    (hrel : Related ⟨33, head, ⟨left, bank values ++ false :: tail⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (shiftTime values + 1) finish [] ∧
      Related ⟨35, head + (shiftTime values : Int) - 1,
        moveLeft ⟨shiftedLeft values left, false :: tail⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (shiftTime values + 1)
        (mapConfig finish) [] ∧ 0 < shiftTime values + 1 := by
  have hb := shift_bank_stop values head left tail
  have hs := advance_sound raw rawLabels hrel (shiftTime values + 1)
  change Related (rawSystem.advance ⟨33, head, ⟨left, bank values ++ false :: tail⟩⟩
    (shiftTime values + 1)) _ ∧
      rawSystem.wordFrom ⟨33, head, ⟨left, bank values ++ false :: tail⟩⟩
        (shiftTime values + 1) = _ at hs
  rw [hb.endpoint, hb.output] at hs
  let finish := (machineWordSystem raw rawLabels).advance c (shiftTime values + 1)
  have hp : (machineWordSystem raw rawLabels).Block c (shiftTime values + 1) finish [] :=
    ⟨rfl, hs.2.symm⟩
  exact ⟨finish, hp, hs.1, BootstrapScan.mapped_block hp, by omega⟩

example : bank [0, 1, 3] =
    [true, false, true, true, false, true, true, true, true, false] := by decide
example : shiftTime [0, 1, 3] = 10 := by decide
example : raw.table.row 33 false ≠ ⟨false, .right, 35, false⟩ := by decide
example : rawLabels.at 33 true = none ∧ rawLabels.at 34 false = none := by decide

end PASoundness.M236.UnaryShift
