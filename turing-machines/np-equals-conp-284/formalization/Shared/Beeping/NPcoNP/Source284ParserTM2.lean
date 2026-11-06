import Shared.Beeping.NPcoNP.Source284ParserOutputs
import Shared.Beeping.NPcoNP.Source284RawParseTM2

/-! Canonical polynomial-time front end for the selected 284 source's
marker/payload parser. Both output fields are raw bit lists: the first is a
unary clock (its bits are irrelevant), and the second is the little-endian
source program. No source-evaluator or machine-table refinement is asserted. -/

namespace Shared.Beeping.NPcoNP.Source284ParserTM2

open Shared.Beeping.NPcoNP.Source284ParserOutputs
open Shared.Beeping.NPcoNP.Source284RawParse
open Shared.Codes.BitNumeralCompare (value)

def parse (xs : List Bool) : List Bool × List Bool := outputs (payload xs)

theorem parse_isPolyTime : ComplexityTheory.IsPolyTime parse :=
  Shared.ComplexityBridge.TM2Compose.isPolyTime_comp payload outputs
    Source284RawParseTM2.payload_isPolyTime outputs_isPolyTime

/-- The clock is a list of exactly the source's parsed number of steps. -/
theorem clock_length (xs : List Bool) :
    (parse xs).1.length = Source284Parser.length (value xs) := by
  simp [parse, outputs, Source284RawParse.parse_length]

/-- The description is returned as the raw little-endian bits used by the
source bit-list evaluator; arbitrary redundant input zeros are accepted. -/
theorem description_value (xs : List Bool) :
    value (parse xs).2 = Source284Parser.description (value xs) := by
  simpa [parse, outputs] using (Source284RawParse.parse_description_bits xs).symm

end Shared.Beeping.NPcoNP.Source284ParserTM2
