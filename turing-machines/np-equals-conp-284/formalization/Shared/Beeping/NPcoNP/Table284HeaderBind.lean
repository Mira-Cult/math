import Shared.Beeping.NPcoNP.Table284Ascii
import Shared.Beeping.NPcoNP.Table284Data

/-! Assemble a complete-table parsing result from exact line splitting and
the parser's checked body result. This is conditional and does not identify
the preserved table bytes or establish the body result. -/
namespace Shared.Beeping.NPcoNP.Table284Ascii
open Shared.Beeping.NPcoNP.Table284

theorem parseChars_of_lines (input : List Char) (rest : List (List Char))
    (hlines : split '\n' input =
      "#! format beeper-events-v1".toList :: "#! states 284".toList ::
      "#! start 0".toList :: "#! blank 0".toList :: "#! head 0".toList :: rest)
    (hbody : rows 284 0 rest = some data.2) :
    parseChars input = some (284, data) := by
  change parseChars input = some (284, ((0, (false, (0 : Int))), data.2))
  unfold parseChars
  rw [hlines]
  simp [header, split, nat, digitsAux, digit, bit, hbody]

end Shared.Beeping.NPcoNP.Table284Ascii
