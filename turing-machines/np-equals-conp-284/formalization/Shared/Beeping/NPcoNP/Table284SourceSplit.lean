import Shared.Beeping.NPcoNP.Table284SourceClean

/-! Staged character splitting for the pinned event-table text. This module
does not establish that the subsequent row parser accepts these lines. -/
namespace Shared.Beeping.NPcoNP.Table284SourceLines

open Shared.Beeping.NPcoNP.Table284Ascii
open Shared.Beeping.NPcoNP.Table284.SourceChars
open Shared.Beeping.NPcoNP.Table284LineData
open Shared.Beeping.TableBits

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem allLines_clean (line : List Char) (h : line ∈ allLines) : '\n' ∉ line := by
  have hc := List.all_eq_true.mp noNewlines_true line h
  exact of_decide_eq_true hc

theorem source_split : split '\n' source.toList = allLines := by
  rw [source_toList, source_join]
  exact split_joinLines '\n' allLines (by decide) allLines_clean

end Shared.Beeping.NPcoNP.Table284SourceLines
