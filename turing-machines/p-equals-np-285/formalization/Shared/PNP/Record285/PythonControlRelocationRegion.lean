import Shared.PNP.Record285.PythonControlRelocationStep

/-! The common decoder's finite row and edge certificate supplies the
premises of the generic single-step relocation theorem. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlRelocationRegion
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlRelocation
open Shared.PNP.Record285.PythonControlRelocationStep

instance (line : Line) : Decidable (Allowed line) := by
  cases line <;> simp [Allowed] <;> infer_instance

def allowedCheck (i : Nat) : Bool :=
  match code[47+i]? with
  | none => false
  | some line => decide (Allowed line)

theorem allowed_checks : (List.range 18).all allowedCheck = true := by decide

theorem decoder_row (i : Nat) (hi : i < 18) :
    ∃ line, code[47+i]? = some line ∧ code[47+i+47]? = some (unindent line) ∧
      Allowed line ∧ Edges (47+i) line := by
  have ha : allowedCheck i = true :=
    (List.all_eq_true).1 allowed_checks i (List.mem_range.2 hi)
  have hr := rows_match i (by omega)
  have he := edges_match i (by omega)
  cases hline : code[47+i]? with
  | none => simp [allowedCheck,hline] at ha
  | some line =>
    have hall : Allowed line := of_decide_eq_true (by simpa [allowedCheck,hline] using ha)
    rw [hline] at hr
    have hm : code[47+i+47]? = some (unindent line) := by
      simpa only [Option.map, Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr.symm
    refine ⟨line,rfl,hm,hall,?_⟩
    unfold edgeCheck at he
    rw [hline] at he
    cases line <;> simp only [Edges]
    all_goals
      apply of_decide_eq_true at he
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he

end Shared.PNP.Record285.PythonControlRelocationRegion
