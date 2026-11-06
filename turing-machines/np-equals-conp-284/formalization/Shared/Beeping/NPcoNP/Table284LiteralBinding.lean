import Shared.Beeping.NPcoNP.Table284SourceSplit
import Shared.Beeping.NPcoNP.Table284HeaderBind
import Shared.Beeping.NPcoNP.Table284RowCoverage
import Shared.Beeping.NPcoNP.Table284

/-! Exact parser binding for the table text embedded at elaboration time.
This proves a finite data identity; it does not prove correctness of the
machine's infinite execution. -/
namespace Shared.Beeping.NPcoNP.Table284LiteralBinding
open Shared.Beeping.NPcoNP.Table284Ascii
open Shared.Beeping.NPcoNP.Table284.SourceChars
open Shared.Beeping.NPcoNP.Table284SourceLines
open Shared.Beeping.NPcoNP.Table284LineData
open Shared.Beeping.NPcoNP.Table284RowCoverage
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.TableBits

theorem source_parses : parse source = some (284, Table284.data) := by
  change parseChars source.toList = some (284, Table284.data)
  apply parseChars_of_lines source.toList (lines ++ [[]])
  · simpa only [allLines, headers, List.append_assoc, List.cons_append, List.nil_append] using source_split
  · exact parsed_rows

/-- Require the declared state count to be 284 before interpreting the raw
rows as the shared finite-machine model. -/
def parseMachine (s : String) : Option (Shared.Beeping.Machines.Machine 284) := do
  let (n, d) ← parse s
  if n = 284 then parseData 284 d else none

theorem source_parses_to_machine : parseMachine source = some machine := by
  simp [parseMachine, source_parses, parse_generated_data]

end Shared.Beeping.NPcoNP.Table284LiteralBinding
