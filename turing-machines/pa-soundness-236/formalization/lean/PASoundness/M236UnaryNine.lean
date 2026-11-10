import PASoundness.M236UnaryCodec
import PASoundness.M236UnaryEntry
import PASoundness.RegisterMachine

/-! An explicit nine-natural-register interface for the unary bank codec.
This identifies the values in the local shift contract; it does not claim
that the selected source program has reached a shift configuration. -/
namespace PASoundness.M236.UnaryNine
open PASoundness.M236.UnaryShift PASoundness.M236.UnaryCodec
open Shared.Beeping Shared.Beeping.Machines PASoundness.M236.FiniteTape

def values (registers : PASoundness.RegisterMachine.Bank 9) : List Nat :=
  List.ofFn registers

@[simp] theorem values_length (registers : PASoundness.RegisterMachine.Bank 9) :
    (values registers).length = 9 := by simp [values]

theorem values_get (registers : PASoundness.RegisterMachine.Bank 9) (i : Fin 9) :
    (values registers)[i.val]'(by simp [values, i.isLt]) = registers i := by
  change (List.ofFn registers)[i.val]'(by simp [i.isLt]) = registers i
  rw [List.getElem_ofFn]

theorem values_nonempty (registers : PASoundness.RegisterMachine.Bank 9) :
    values registers ≠ [] := by
  intro h
  have hl := values_length registers
  rw [h] at hl
  contradiction

/-- The same nine arbitrary register values decode on both sides of the
shift, with the terminal separator and suffix retained. -/
theorem nine_values_decode (registers : PASoundness.RegisterMachine.Bank 9)
    (tail : List Bool) :
    decodeBank 9 (bank (values registers) ++ false :: tail) =
      some (values registers, false :: tail) ∧
    decodeShifted 9 (shiftedWord (values registers) ++ false :: tail) =
      some (values registers, false :: tail) := by
  constructor
  · simpa using decode_bank (values registers) (false :: tail)
  · simpa using decode_shifted (values registers) tail

/-- A literal raw/quotient shift for any nine source-register values. The
precondition describes the full tape at state 33; reaching it is a separate
runtime invariant. -/
theorem physical_nine (registers : PASoundness.RegisterMachine.Bank 9)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨33, head, ⟨left, bank (values registers) ++ false :: tail⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (shiftTime (values registers)) finish [] ∧
      Related ⟨33, head + (shiftTime (values registers) : Int),
        ⟨(shiftedWord (values registers)).reverse ++ left, false :: tail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (shiftTime (values registers))
        (mapConfig finish) [] ∧
      decodeBank 9 (bank (values registers) ++ false :: tail) =
        some (values registers, false :: tail) ∧
      decodeShifted 9 (shiftedWord (values registers) ++ false :: tail) =
        some (values registers, false :: tail) ∧
      0 < shiftTime (values registers) := by
  simpa only [values_length] using
    physical_preserves_values (values registers) (values_nonempty registers) head left tail c hrel

/-- The same contract permits any finite reserve after the nine values.
The shift preserves and decodes every reserve block as well. -/
theorem physical_nine_with_reserve (registers : PASoundness.RegisterMachine.Bank 9)
    (reserve : List Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨33, head, ⟨left, bank (values registers ++ reserve) ++ false :: tail⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (shiftTime (values registers ++ reserve)) finish [] ∧
      Related ⟨33, head + (shiftTime (values registers ++ reserve) : Int),
        ⟨(shiftedWord (values registers ++ reserve)).reverse ++ left, false :: tail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (shiftTime (values registers ++ reserve)) (mapConfig finish) [] ∧
      decodeBank (9 + reserve.length) (bank (values registers ++ reserve) ++ false :: tail) =
        some (values registers ++ reserve, false :: tail) ∧
      decodeShifted (9 + reserve.length) (shiftedWord (values registers ++ reserve) ++ false :: tail) =
        some (values registers ++ reserve, false :: tail) ∧
      0 < shiftTime (values registers ++ reserve) := by
  have hne : values registers ++ reserve ≠ [] := by
    intro h
    have hlength := congrArg List.length h
    simp only [List.length_append, values_length, List.length_nil] at hlength
    omega
  have hlen : (values registers ++ reserve).length = 9 + reserve.length := by simp
  simpa only [hlen] using
    physical_preserves_values (values registers ++ reserve) hne head left tail c hrel

def zeroRegisters : PASoundness.RegisterMachine.Bank 9 := fun _ => 0

theorem zero_values : values zeroRegisters = List.replicate 9 0 := by decide

/-- The certified initial 1,910 zero blocks admit a nine-plus-reserve
decomposition. Identifying these positions with source register names is a
separate compiler invariant. -/
theorem initial_decomposition :
    bank (values zeroRegisters ++ List.replicate 1901 0) =
      bank (List.replicate 1910 0) := by
  rw [zero_values, List.replicate_append_replicate]

def candidateEntryTape : Tape :=
  ⟨[false, true, true, false, false, false, false, false, false, false],
    List.replicate 3820 false ++
      (false :: bank (values zeroRegisters ++ List.replicate 1901 0))⟩

theorem initial_nine_plus_reserve :
    Related ⟨78, -3818, candidateEntryTape⟩
      ((machineWordSystem machine machineLabels).run 89821408) ∧
      (machineWordSystem machine machineLabels).prefixWord 89821408 = [] := by
  have h := UnaryEntry.selected_initial_bank
  have ht : UnaryEntry.entryBankTape = candidateEntryTape := by
    simp only [UnaryEntry.entryBankTape, candidateEntryTape, initial_decomposition]
  rw [ht] at h
  exact h

def largeBank : PASoundness.RegisterMachine.Bank 9 :=
  fun i => if i.val = 8 then 1000000 else 0

example : largeBank 8 = 1000000 := by decide
example (tail : List Bool) :
    decodeBank 9 (bank (values largeBank) ++ false :: tail) =
      some (values largeBank, false :: tail) := (nine_values_decode largeBank tail).1

end PASoundness.M236.UnaryNine
