import Shared.Beeping.NPcoNP.Table284SourceChars
import Shared.Beeping.NPcoNP.Table284ParseStages
import Shared.Beeping.NPcoNP.Table284LineData

/-! Exact joining of every embedded source character, including final
newline, to the shared literal lines. No row-parser claim is made here. -/
namespace Shared.Beeping.NPcoNP.Table284SourceLines

open Shared.Beeping.NPcoNP.Table284Ascii
open Shared.Beeping.NPcoNP.Table284.SourceChars
open Shared.Beeping.NPcoNP.Table284LineData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def headers : List (List Char) :=
  ["#! format beeper-events-v1".toList, "#! states 284".toList,
   "#! start 0".toList, "#! blank 0".toList, "#! head 0".toList]

/-- The final empty line records the literal file's trailing newline. -/
def allLines : List (List Char) := headers ++ lines ++ [[]]

/-- All embedded source characters are covered, not only their hash. -/
theorem source_join : chars = joinLines '\n' allLines := by rfl

end Shared.Beeping.NPcoNP.Table284SourceLines
