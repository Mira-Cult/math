import Shared.Beeping.NPcoNP.Source284EmptyBranchAdapter
import Shared.Beeping.NPcoNP.Source284MaterializeRows

/-! Executable finite-row data for the zero-prefix adapter. This construction
has no asserted polynomial generation cost and does not build a guarded
verifier or a physical beeper. -/
namespace Shared.Beeping.NPcoNP.Source284EmptyBranchFinite

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284EncodedRows

/-- Decode every finite row tuple, attach the two explicit adapter states,
and materialize exactly the allocated rows. Invalid tuple destinations are
still data; closure is separately checked. -/
def adapt (original : EncRows) : EncRows :=
  Source284MaterializeRows.rows (original.length+2)
    (Source284EmptyBranchAdapter.table (Source284ListTables.table (decodeRows original)))

theorem adapt_length (original : EncRows) : (adapt original).length = original.length+2 := by
  simp [adapt,Source284MaterializeRows.rows_length]

theorem adapt_table (original : EncRows) (q : Nat) (hq : q < original.length+2) (read : Bool) :
    Source284ListTables.table (decodeRows (adapt original)) q read =
      Source284EmptyBranchAdapter.table (Source284ListTables.table (decodeRows original)) q read := by
  exact Source284MaterializeRows.table_agrees _ _ q hq read

theorem adapt_closed (original : EncRows) (hn : 0 < original.length)
    (hv : Source284ListTables.valid (decodeRows original) = true) :
    Closed (adapt original).length (Source284ListTables.table (decodeRows (adapt original))) := by
  apply Source284MaterializeRows.table_closed
  apply Source284EmptyBranchAdapter.closed _ _ hn
  simpa using Source284ListTables.valid_closed (decodeRows original) hv

/-- Materializing and decoding the adapter preserves the full encoded source
numeral, including an arbitrary high tail. -/
theorem adapt_encode (original : EncRows) (tail : Nat) :
    encode (adapt original).length (Source284ListTables.table (decodeRows (adapt original))) tail =
      encode (original.length+2)
        (Source284EmptyBranchAdapter.table (Source284ListTables.table (decodeRows original))) tail :=
  Source284MaterializeRows.encode_agrees _ _ tail

/-- The literal finite row data accept every zero-prefix input in one source
iteration for every certificate. -/
theorem adapt_empty_attempt (original : EncRows) (tail input certificate : Nat)
    (hzero : Source284Parser.length input = 0) :
    Source284Relative.accepts
      (encode (adapt original).length (Source284ListTables.table (decodeRows (adapt original))) tail)
      input certificate 1 = true := by
  rw [adapt_encode]
  exact Source284EmptyBranchAdapter.encoded_empty_attempt _ _ _ _ _ hzero

/-- On odd inputs the finite adapter agrees with the original finite table's
entire bounded search after exactly two setup iterations. -/
theorem adapt_odd_search (original : EncRows) (tail input fuel bound : Nat)
    (hn : 0 < original.length)
    (hv : Source284ListTables.valid (decodeRows original) = true) (hodd : input % 2 = 1) :
    Source284Relative.acceptBound
      (encode (adapt original).length (Source284ListTables.table (decodeRows (adapt original))) tail)
      input (fuel+2) bound =
    Source284Relative.acceptBound
      (encode original.length (Source284ListTables.table (decodeRows original)) 0) input fuel bound := by
  rw [adapt_encode]
  apply Source284EmptyBranchAdapter.encoded_odd_search _ _ _ _ _ _ hn _ hodd
  simpa using Source284ListTables.valid_closed (decodeRows original) hv

end Shared.Beeping.NPcoNP.Source284EmptyBranchFinite
