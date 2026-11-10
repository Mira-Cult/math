import PASoundness.M236UnaryShift

/-! Decoding the unbounded unary runs on either side of the literal shift. -/
set_option maxRecDepth 8192
namespace PASoundness.M236.UnaryCodec
open PASoundness.M236.UnaryShift
open Shared.Beeping Shared.Beeping.Machines PASoundness.M236.FiniteTape

/-- Count a finite leading run of ones, leaving the first zero unconsumed. -/
def takeOnes : List Bool → Nat × List Bool
  | [] => (0, [])
  | false :: rest => (0, false :: rest)
  | true :: rest =>
    let (n, tail) := takeOnes rest
    (n + 1, tail)

theorem takeOnes_replicate (n : Nat) (tail : List Bool) :
    takeOnes (List.replicate n true ++ false :: tail) = (n, false :: tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, takeOnes, ih]

/-- The trailing separator is consumed for each ordinary bank block. -/
def decodeBank : Nat → List Bool → Option (List Nat × List Bool)
  | 0, tape => some ([], tape)
  | n + 1, tape =>
    let (ones, tail) := takeOnes tape
    match ones, tail with
    | value + 1, false :: rest =>
      (decodeBank n rest).map fun (values, suffix) => (value :: values, suffix)
    | _, _ => none

theorem decode_bank (values : List Nat) (tail : List Bool) :
    decodeBank values.length (bank values ++ tail) = some (values, tail) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.length_cons, bank, List.cons_append, List.append_assoc]
    simp [decodeBank, takeOnes, takeOnes_replicate, ih]

/-- In the shifted format the leading zero is consumed, and the next zero
is retained for the next block. The final zero is an explicit sentinel. -/
def decodeShifted : Nat → List Bool → Option (List Nat × List Bool)
  | 0, tape => some ([], tape)
  | n + 1, false :: tape =>
    let (ones, rest) := takeOnes tape
    match ones with
    | 0 => none
    | value + 1 =>
      (decodeShifted n rest).map fun (values, suffix) => (value :: values, suffix)
  | _ + 1, _ => none

theorem shifted_has_separator (values : List Nat) (tail : List Bool) :
    ∃ rest, shiftedWord values ++ false :: tail = false :: rest := by
  cases values with
  | nil => exact ⟨tail, rfl⟩
  | cons value values =>
    exact ⟨(List.replicate (value + 1) true ++ shiftedWord values) ++ false :: tail, rfl⟩

/-- Decoding before and after the physical shift yields the same arbitrary
finite values; the final separator and all later tape cells are retained. -/
theorem decode_shifted (values : List Nat) (tail : List Bool) :
    decodeShifted values.length (shiftedWord values ++ false :: tail) =
      some (values, false :: tail) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    obtain ⟨suffix, hs⟩ := shifted_has_separator rest tail
    have hrun : takeOnes (List.replicate (value + 1) true ++
        (shiftedWord rest ++ false :: tail)) =
        (value + 1, shiftedWord rest ++ false :: tail) := by
      rw [hs]
      exact takeOnes_replicate _ _
    simp only [List.length_cons, shiftedWord, List.cons_append, List.append_assoc]
    simp [decodeShifted, hrun, ih]

/-- For any nonempty finite bank, the raw and quotient executions have a
positive silent block, retain the whole tape, and encode exactly the same
values before and after the shift. -/
theorem physical_preserves_values (values : List Nat) (hne : values ≠ [])
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨33, head, ⟨left, bank values ++ false :: tail⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (shiftTime values) finish [] ∧
      Related ⟨33, head + (shiftTime values : Int),
        ⟨(shiftedWord values).reverse ++ left, false :: tail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (shiftTime values)
        (mapConfig finish) [] ∧
      decodeBank values.length (bank values ++ false :: tail) = some (values, false :: tail) ∧
      decodeShifted values.length (shiftedWord values ++ false :: tail) = some (values, false :: tail) ∧
      0 < shiftTime values := by
  have hb := shift_bank values head left (false :: tail)
  have hs := advance_sound raw rawLabels hrel (shiftTime values)
  change Related (rawSystem.advance ⟨33, head, ⟨left, bank values ++ false :: tail⟩⟩
    (shiftTime values)) _ ∧
      rawSystem.wordFrom ⟨33, head, ⟨left, bank values ++ false :: tail⟩⟩
        (shiftTime values) = _ at hs
  rw [hb.1.endpoint, hb.1.output] at hs
  rw [shiftedLeft_eq] at hs
  let finish := (machineWordSystem raw rawLabels).advance c (shiftTime values)
  have hp : (machineWordSystem raw rawLabels).Block c (shiftTime values) finish [] :=
    ⟨rfl, hs.2.symm⟩
  exact ⟨finish, hp, hs.1, BootstrapScan.mapped_block hp, decode_bank values _,
    decode_shifted values tail, hb.2 hne⟩

example : decodeBank 2 [true, false, true, true, false, true] = some ([0, 1], [true]) := by decide
example : decodeBank 1 [false, true] = none := by decide
example : decodeShifted 1 [false, false] = none := by decide

end PASoundness.M236.UnaryCodec
