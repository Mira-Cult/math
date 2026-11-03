import Shared.ComplexityBridge.TM0FiniteProgram
import Shared.Codes.FiniteProgramRepair

/-! Relate finite-program list tapes modulo blank padding. This is needed when
a concrete input wrapper leaves extra false cells around its output. -/
namespace Shared.Codes.FiniteProgramTapeEquiv
open Turing
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.TM0FiniteProgram

def TapeRel (a b : Shared.Codes.FinitePrograms.Tape) : Prop := tape a = tape b

def StatusRel : Status → Status → Prop
  | none, none => True
  | some (.inl a), some (.inl b) => a = b
  | some (.inr a), some (.inr b) => a.1 = b.1 ∧ TapeRel a.2 b.2
  | _, _ => False

theorem tape_head {a b : Shared.Codes.FinitePrograms.Tape} (h : TapeRel a b) : a.2.1 = b.2.1 := by
  exact congrArg Turing.Tape.head h

theorem move_related (leftward written : Bool) (a b : Shared.Codes.FinitePrograms.Tape)
    (h : TapeRel a b) : TapeRel (moveTape leftward written a) (moveTape leftward written b) := by
  cases leftward with
  | false =>
    have ha := tape_move a written Dir.right
    have hb := tape_move b written Dir.right
    change tape (moveTape false written a) = ((tape a).write written).move .right at ha
    change tape (moveTape false written b) = ((tape b).write written).move .right at hb
    unfold TapeRel at h ⊢
    rw [ha,hb,h]
  | true =>
    have ha := tape_move a written Dir.left
    have hb := tape_move b written Dir.left
    change tape (moveTape true written a) = ((tape a).write written).move .left at ha
    change tape (moveTape true written b) = ((tape b).write written).move .left at hb
    unfold TapeRel at h ⊢
    rw [ha,hb,h]

theorem execute_related (row : Row) (a b : Shared.Codes.FinitePrograms.Tape)
    (h : TapeRel a b) : StatusRel (executeRow row a) (executeRow row b) := by
  rcases row with ⟨w,dir,next,tag⟩
  cases tag with
  | zero => exact ⟨rfl,move_related (!dir) w a b h⟩
  | succ tag => cases tag with
    | zero => rfl
    | succ tag => cases tag with
      | zero => rfl
      | succ tag => trivial

theorem step_related (p : Program) (a b : Config)
    (hq : a.1 = b.1) (ht : TapeRel a.2 b.2) : StatusRel (step p a) (step p b) := by
  have hh : a.2.2.1 = b.2.2.1 := tape_head ht
  cases hp : p[a.1]? with
  | none =>
    have hp' : p[b.1]? = none := by rw [← hq]; exact hp
    simp [step,hp,hp',StatusRel]
  | some rows =>
    have ha : rowAt p a = some (if a.2.2.1 then rows.2 else rows.1) := by simp [rowAt,hp]
    have hb : rowAt p b = some (if a.2.2.1 then rows.2 else rows.1) := by simp [rowAt,← hq,hp,← hh]
    rw [Shared.ComplexityBridge.CircuitTable.step_eq_executeRow p a _ ha,
      Shared.ComplexityBridge.CircuitTable.step_eq_executeRow p b _ hb]
    exact execute_related _ a.2 b.2 ht

theorem advance_related (p : Program) (a b : Status) (h : StatusRel a b) :
    StatusRel (advance p a) (advance p b) := by
  cases a with
  | none => cases b <;> simp [StatusRel] at h ⊢
  | some av =>
    cases av with
    | inl x =>
      cases b with
      | none => simp [StatusRel] at h
      | some bv => cases bv with
        | inl y => simp only [StatusRel] at h; subst y; rfl
        | inr c => simp [StatusRel] at h
    | inr x =>
      cases b with
      | none => simp [StatusRel] at h
      | some bv => cases bv with
        | inl y => simp [StatusRel] at h
        | inr y => exact step_related p x y h.1 h.2

theorem run_related (p : Program) (a b : Config)
    (hq : a.1 = b.1) (ht : TapeRel a.2 b.2) (n : Nat) :
    StatusRel (run p a n) (run p b n) := by
  induction n with
  | zero => exact ⟨hq,ht⟩
  | succ n ih => exact advance_related p _ _ ih

def result : Status → Option Bool
  | some (.inl b) => some b
  | _ => none

theorem result_related (a b : Status) (h : StatusRel a b) : result a = result b := by
  cases a with
  | none => cases b <;> simp [StatusRel,result] at h ⊢
  | some av => cases av with
    | inl x =>
      cases b with
      | none => simp [StatusRel] at h
      | some bv => cases bv with
        | inl y => simp only [StatusRel] at h; subst y; rfl
        | inr c => simp [StatusRel] at h
    | inr x =>
      cases b with
      | none => simp [StatusRel] at h
      | some bv => cases bv with
        | inl y => simp [StatusRel] at h
        | inr y => rfl

/-- Every result, including timeout and invalid execution, is unchanged by
blank padding on either side of the head. -/
theorem run_result_congr (p : Program) (a b : Config) (hq : a.1 = b.1)
    (ht : TapeRel a.2 b.2) (n : Nat) : result (run p a n) = result (run p b n) :=
  result_related _ _ (run_related p a b hq ht n)

end Shared.Codes.FiniteProgramTapeEquiv
