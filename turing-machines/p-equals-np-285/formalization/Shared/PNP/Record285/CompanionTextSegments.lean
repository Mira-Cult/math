import Shared.PNP.Record285.TextSegments

/-! The same exact newline reconstruction for the 286-state companion. -/
namespace Shared.PNP.Record285.CompanionTextSegments
open Shared.PNP.Record285
open Shared.PNP.Record285.TextSegments (linesChars clean split_lines)

def header : List String := ["#! format beeper-v1", "#! states 286", "#! start 0",
  "#! beep 1", "#! blank 0", "#! head 0"]

theorem parse_of_lines (lines : List String) (result : List RawRow)
    (hc : lines.all clean = true)
    (hp : lines.mapM (fun s => Companion.parseRow s.toList) = some result)
    (htext : Companion.literal = String.ofList (linesChars (header ++ lines))) :
    Companion.parse = some result := by
  have hclean : (header ++ lines).all clean = true := by simpa [header, clean] using hc
  have hs := split_lines (header ++ lines) hclean
  unfold Companion.parse
  rw [htext, String.toList_ofList, hs]
  simpa [header, guard, Function.comp_def, List.mapM_map] using hp

theorem parse_append (ls rs : List String) (p q : List RawRow)
    (hp : ls.mapM (fun s => Companion.parseRow s.toList) = some p)
    (hq : rs.mapM (fun s => Companion.parseRow s.toList) = some q) :
    (ls ++ rs).mapM (fun s => Companion.parseRow s.toList) = some (p ++ q) := by
  simp [List.mapM_append, hp, hq]

end Shared.PNP.Record285.CompanionTextSegments
