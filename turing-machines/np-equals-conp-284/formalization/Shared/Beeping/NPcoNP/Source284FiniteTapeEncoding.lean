import Shared.Beeping.NPcoNP.Source284FiniteTapeStep
import Shared.Codes.BitNumeralCompare

/-! Reconcile the recovered finite-tape step's local numeral notation with
the shared low-endian bitstring value. This is an encoding identity, not a
finite-program compiler or a run-level correctness theorem. -/
namespace Shared.Beeping.NPcoNP.Source284FiniteTapeStep

theorem value_eq_shared (xs : List Bool) :
    value xs = Shared.Codes.BitNumeralCompare.value xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [value, Shared.Codes.BitNumeralCompare.value, ih, digit]
    omega

/-- The represented control state is independent of tape orientation. -/
@[simp] theorem represented_state (t : Shared.Codes.FinitePrograms.Tape)
    (reverse : Bool) (state : Nat) : (represented t reverse state).state = state := by
  cases reverse <;> rfl

/-- Either orientation exposes the physical head as the low forward bit. -/
theorem represented_read (t : Shared.Codes.FinitePrograms.Tape)
    (reverse : Bool) (state : Nat) :
    (represented t reverse state).right % 2 = digit t.2.1 := by
  cases reverse <;> cases h : t.2.1 <;> simp [represented, digit, h] <;> omega

/-- Facing right, the head belongs to the numeric forward half. -/
theorem represented_forward (t : Shared.Codes.FinitePrograms.Tape) (state : Nat) :
    represented t false state =
      ⟨Shared.Codes.BitNumeralCompare.value t.1,
       Shared.Codes.BitNumeralCompare.value (t.2.1 :: t.2.2), state⟩ := by
  simp [represented, value_eq_shared, Shared.Codes.BitNumeralCompare.value, digit,
    Nat.add_comm]

/-- Facing left swaps the two physical sides while retaining the head. -/
theorem represented_reverse (t : Shared.Codes.FinitePrograms.Tape) (state : Nat) :
    represented t true state =
      ⟨Shared.Codes.BitNumeralCompare.value t.2.2,
       Shared.Codes.BitNumeralCompare.value (t.2.1 :: t.1), state⟩ := by
  simp [represented, value_eq_shared, Shared.Codes.BitNumeralCompare.value, digit,
    Nat.add_comm]

end Shared.Beeping.NPcoNP.Source284FiniteTapeStep
