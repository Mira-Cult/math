import Shared.Beeping.NPcoNP.Table284SourceJoin
import Shared.Beeping.NPcoNP.Table284CleanShard00
import Shared.Beeping.NPcoNP.Table284CleanShard01
import Shared.Beeping.NPcoNP.Table284CleanShard02

/-! Aggregate checked newline-free line chunks without re-evaluating them. -/
namespace Shared.Beeping.NPcoNP.Table284SourceLines
open Shared.Beeping.NPcoNP.Table284LineData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def noNewlines : Bool := allLines.all fun line => decide ('\n' ∉ line)

theorem noNewlines_true : noNewlines = true := by
  have hlines : lines.all (fun line => decide ('\n' ∉ line)) = true := by
    unfold lines
    rw [List.all_append, clean28]
    simp only [Bool.and_true]
    rw [List.all_append, clean27]
    simp only [Bool.and_true]
    rw [List.all_append, clean26]
    simp only [Bool.and_true]
    rw [List.all_append, clean25]
    simp only [Bool.and_true]
    rw [List.all_append, clean24]
    simp only [Bool.and_true]
    rw [List.all_append, clean23]
    simp only [Bool.and_true]
    rw [List.all_append, clean22]
    simp only [Bool.and_true]
    rw [List.all_append, clean21]
    simp only [Bool.and_true]
    rw [List.all_append, clean20]
    simp only [Bool.and_true]
    rw [List.all_append, clean19]
    simp only [Bool.and_true]
    rw [List.all_append, clean18]
    simp only [Bool.and_true]
    rw [List.all_append, clean17]
    simp only [Bool.and_true]
    rw [List.all_append, clean16]
    simp only [Bool.and_true]
    rw [List.all_append, clean15]
    simp only [Bool.and_true]
    rw [List.all_append, clean14]
    simp only [Bool.and_true]
    rw [List.all_append, clean13]
    simp only [Bool.and_true]
    rw [List.all_append, clean12]
    simp only [Bool.and_true]
    rw [List.all_append, clean11]
    simp only [Bool.and_true]
    rw [List.all_append, clean10]
    simp only [Bool.and_true]
    rw [List.all_append, clean09]
    simp only [Bool.and_true]
    rw [List.all_append, clean08]
    simp only [Bool.and_true]
    rw [List.all_append, clean07]
    simp only [Bool.and_true]
    rw [List.all_append, clean06]
    simp only [Bool.and_true]
    rw [List.all_append, clean05]
    simp only [Bool.and_true]
    rw [List.all_append, clean04]
    simp only [Bool.and_true]
    rw [List.all_append, clean03]
    simp only [Bool.and_true]
    rw [List.all_append, clean02]
    simp only [Bool.and_true]
    rw [List.all_append, clean01]
    simp only [Bool.and_true]
    exact clean00
  have hh : headers.all (fun line => decide ('\n' ∉ line)) = true := by decide
  simp only [noNewlines, allLines, List.all_append, hh, hlines, Bool.true_and]
  rfl

end Shared.Beeping.NPcoNP.Table284SourceLines
