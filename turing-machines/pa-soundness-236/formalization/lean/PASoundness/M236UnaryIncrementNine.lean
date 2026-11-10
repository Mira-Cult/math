import PASoundness.M236UnaryIncrement
import PASoundness.M236UnaryNine

/-! Link the literal local increment segment to the independent nine-register
operation. The physical entry and return-to-control conditions remain explicit. -/
set_option maxRecDepth 8192
namespace PASoundness.M236.UnaryIncrementNine

open Shared.Beeping Shared.Beeping.Machines PASoundness.M236.FiniteTape
open PASoundness.M236.UnaryShift PASoundness.M236.UnaryIncrement
open PASoundness.M236.UnaryNine PASoundness.RegisterMachine

def before (registers : Bank 9) (r : Fin 9) : List Nat :=
  (values registers).take r.val

def after (registers : Bank 9) (r : Fin 9) : List Nat :=
  (values registers).drop (r.val + 1)

theorem values_write (registers : Bank 9) (r : Fin 9) (value : Nat) :
    values (write registers r value) = (values registers).set r.val value := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hj9 : j < 9 := by simpa using hj
    rw [List.getElem_set]
    simp only [values, List.getElem_ofFn]
    by_cases he : r.val = j
    · have hf : (⟨j, hj9⟩ : Fin 9) = r := Fin.ext he.symm
      simp [he, hf, write]
    · have hf : (⟨j, hj9⟩ : Fin 9) ≠ r := by
        intro h
        apply he
        exact (congrArg Fin.val h).symm
      simp [he, hf, write]

theorem values_split (registers : Bank 9) (r : Fin 9) :
    values registers = before registers r ++ registers r :: after registers r := by
  have hi : r.val < (values registers).length := by simp [r.isLt]
  have h := List.set_getElem_self (as := values registers) (i := r.val) hi
  rw [List.set_eq_take_append_cons_drop, if_pos hi] at h
  have hr := values_get registers r
  simpa only [before, after, hr] using h.symm

theorem values_increment (registers : Bank 9) (r : Fin 9) :
    values (execute (.inc r) registers).bank =
      before registers r ++ (registers r + 1) :: after registers r := by
  change values (write registers r (registers r + 1)) = _
  rw [values_write, List.set_eq_take_append_cons_drop]
  have hi : r.val < (values registers).length := by simp [r.isLt]
  simp only [hi, ↓reduceIte, before, after]

/-- The state-9 zipper precondition contains precisely the source bank
followed by its reserve and a zero cell for expansion. -/
theorem input_linear (registers : Bank 9) (r : Fin 9) (reserve : List Nat)
    (left tail : List Bool) :
    linear ⟨(bank (before registers r)).reverse ++ left,
      List.replicate (registers r + 1) true ++ false ::
        (bank (after registers r ++ reserve) ++ false :: tail)⟩ =
      left.reverse ++ (bank (values registers ++ reserve) ++ false :: tail) := by
  rw [values_split registers r]
  simp [linear, bank_append, bank, List.replicate_succ, List.reverse_append, List.append_assoc]

/-- At the explicit state-9 tape interface, the literal machine performs
the same bank update as the independent nine-register increment operation.
The arbitrary reserve and all other registers are retained. -/
theorem physical_increment_nine (registers : Bank 9) (r : Fin 9) (reserve : List Nat)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨9, head, ⟨(bank (before registers r)).reverse ++ left,
        List.replicate (registers r + 1) true ++ false ::
          (bank (after registers r ++ reserve) ++ false :: tail)⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (duration (registers r) (after registers r ++ reserve)) finish [] ∧
      Related
        ⟨35, head + ((registers r + 2 : Nat) : Int) +
            (shiftTime (after registers r ++ reserve) : Int) - 1,
          moveLeft ⟨shiftedLeft (after registers r ++ reserve)
            (true :: (List.replicate (registers r + 1) true ++
              ((bank (before registers r)).reverse ++ left))), false :: tail⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (duration (registers r) (after registers r ++ reserve)) (mapConfig finish) [] ∧
      linear ⟨(bank (before registers r)).reverse ++ left,
        List.replicate (registers r + 1) true ++ false ::
          (bank (after registers r ++ reserve) ++ false :: tail)⟩ =
        left.reverse ++ (bank (values registers ++ reserve) ++ false :: tail) ∧
      linear (moveLeft ⟨shiftedLeft (after registers r ++ reserve)
        (true :: (List.replicate (registers r + 1) true ++
          ((bank (before registers r)).reverse ++ left))), false :: tail⟩ false) =
        left.reverse ++ (bank (values (execute (.inc r) registers).bank ++ reserve) ++ tail) ∧
      UnaryCodec.decodeBank (9 + reserve.length)
        (bank (values (execute (.inc r) registers).bank ++ reserve) ++ tail) =
        some (values (execute (.inc r) registers).bank ++ reserve, tail) ∧
      0 < duration (registers r) (after registers r ++ reserve) ∧
      (execute (.inc r) registers).success = true ∧
      (execute (.inc r) registers).output = [] := by
  obtain ⟨finish, hp, hr, hq, hw, _, hpos⟩ :=
    physical_increment_in_bank (before registers r) (registers r)
      (after registers r ++ reserve) head left tail c hrel
  have hvalues : before registers r ++ (registers r + 1) :: (after registers r ++ reserve) =
      values (execute (.inc r) registers).bank ++ reserve := by
    rw [values_increment]
    simp [List.append_assoc]
  rw [hvalues] at hw
  refine ⟨finish, hp, hr, hq, input_linear registers r reserve left tail, hw, ?_, hpos, rfl, rfl⟩
  simpa only [List.length_append, values_length] using
    UnaryCodec.decode_bank (values (execute (.inc r) registers).bank ++ reserve) tail

end PASoundness.M236.UnaryIncrementNine
