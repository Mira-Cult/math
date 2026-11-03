import Shared.PNP.Record285.NumericBinding
/-! Generic newline-delimited text reconstruction and parser composition. -/
namespace Shared.PNP.Record285.TextSegments
open Shared.PNP.Record285 Shared.PNP.Record285.NumericBinding Shared.PNP.Record285.NumericTables

def linesChars : List String → List Char
  | [] => []
  | s :: ss => s.toList ++ '\n' :: linesChars ss

def clean (s : String) : Bool := !s.toList.contains '\n'

theorem split_line (line tail : List Char) (h : '\n' ∉ line) :
    splitChars '\n' (line ++ '\n' :: tail) = line :: splitChars '\n' tail := by
  induction line with
  | nil => rfl
  | cons a as ih =>
    have ha : a ≠ '\n' := by simp only [List.mem_cons, not_or] at h; exact Ne.symm h.1
    have hs : '\n' ∉ as := by simp only [List.mem_cons, not_or] at h; exact h.2
    simp only [List.cons_append, splitChars, ih hs]
    simp [ha]

theorem split_lines (lines : List String) (h : lines.all clean = true) :
    splitChars '\n' (linesChars lines) = lines.map String.toList ++ [[]] := by
  induction lines with
  | nil => rfl
  | cons s ss ih =>
    have hh : clean s = true ∧ ss.all clean = true := by simpa using h
    have hc : '\n' ∉ s.toList := by
      simp [clean, List.contains_eq_mem] at hh
      exact hh.1
    simp only [linesChars, split_line s.toList (linesChars ss) hc, ih hh.2,
      List.map_cons, List.cons_append]



def header : List String := ["#! format beeper-events-v1", "#! states 285", "#! start 0", "#! blank 0", "#! head 0"]

theorem parse_of_lines (lines : List String) (result : List RawRow)
    (hc : lines.all clean = true)
    (hp : lines.mapM (fun s => parseRow s.toList) = some result)
    (htext : literal = String.ofList (linesChars (header ++ lines))) :
    Shared.PNP.Record285.parse = some result := by
  have hclean : (header ++ lines).all clean = true := by simpa [header, clean] using hc
  have hs := split_lines (header ++ lines) hclean
  unfold Shared.PNP.Record285.parse
  rw [htext, String.toList_ofList, hs]
  simpa [header, guard, Function.comp_def, List.mapM_map] using hp


theorem parse_append (ls rs : List String) (p q : List RawRow)
    (hp : ls.mapM (fun s => parseRow s.toList) = some p)
    (hq : rs.mapM (fun s => parseRow s.toList) = some q) :
    (ls ++ rs).mapM (fun s => parseRow s.toList) = some (p ++ q) := by
  simp [List.mapM_append, hp, hq]

end Shared.PNP.Record285.TextSegments
