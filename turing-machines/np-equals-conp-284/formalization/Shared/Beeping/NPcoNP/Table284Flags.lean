import Shared.Beeping.NPcoNP.Table284

/-! Finite flag facts for the generated numeric 284-state machine. These do
not prove that its data come from the pinned source text or anything about its
infinite execution. -/
namespace Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.Machines Shared.Beeping.TableBits Shared.Beeping.TableSyntax

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def flagsCheck : Bool :=
  data.2.zipIdx.all (fun (p, i) => (!p.1.2.2.2) && (p.2.2.2.2 == decide (i = 99)))

theorem flagsCheck_true : flagsCheck = true := by decide

theorem data_flags (q : Fin 284) :
    let h : q.val < data.2.length := by rw [rows_length]; exact q.isLt
    let p := data.2[q.val]'h
    p.1.2.2.2 = false ∧ p.2.2.2.2 = decide (q.val = 99) := by
  dsimp only
  have hi : q.val < data.2.zipIdx.length := by simpa [List.length_zipIdx, rows_length] using q.isLt
  have ha := List.all_eq_true.mp flagsCheck_true _ (List.getElem_mem hi)
  simp only [List.getElem_zipIdx, Nat.zero_add, Bool.and_eq_true, beq_iff_eq] at ha
  simpa using ha

private def rawSyntax : Syntax := ((0,(false,(0,0))), data.2)

theorem marked_row_exact (q : Fin 284) (b : Bool) :
    (machine.table.row q b).beep = decide (q.val = 99 ∧ b = true) := by
  have hp : parseData 284 (toData rawSyntax) = some machine := by
    change parseData 284 data = some machine
    exact parse_generated_data
  have hq : q.val < data.2.length := by rw [rows_length]; exact q.isLt
  have hx := lookup_correct hp q b
  simp only [lookup, rawSyntax, List.getElem?_eq_getElem hq, Option.map_some,
    Option.some.injEq] at hx
  have hb := congrArg (fun r : RawRow => r.2.2.2) hx
  have hf := data_flags q
  cases b with
  | false => simpa [rowData] using hb.symm.trans hf.1
  | true => simpa [rowData] using hb.symm.trans hf.2

theorem beepAt_iff (t : Nat) :
    machine.system.BeepAt t ↔
      (machine.system.run t).state.val = 99 ∧
        (machine.system.run t).tape (machine.system.run t).head = true := by
  rw [Machine.beepAt_iff_row_flag, marked_row_exact]
  simp

theorem marked_row : machine.table.row ⟨99, by decide⟩ true =
    ⟨false, .left, ⟨1, by decide⟩, true⟩ := by decide

end Shared.Beeping.NPcoNP.Table284
