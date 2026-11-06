import Shared.Beeping.NPcoNP.Source284EmptyBranchFiniteTM2

/-! Executable validity of the materialized adapter. This proves no verifier
or timeout-guard correctness beyond the imported finite-table results. -/
namespace Shared.Beeping.NPcoNP.Source284EmptyBranchValidity

open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284ListTables
open Shared.Beeping.NPcoNP.Source284EncodedRows

/-- For finite row data, semantic successor closure implies the executable
row-validity check. The converse is `Source284ListTables.valid_closed`. -/
theorem valid_of_closed (rows : Rows) (hclosed : Closed rows.length (table rows)) :
    valid rows = true := by
  apply List.all_eq_true.mpr
  intro pair hmem
  obtain ⟨q,hq,he⟩ := List.mem_iff_getElem.mp hmem
  simp only [Bool.and_eq_true]
  constructor
  · cases hn : pair.1.next with
    | none => simp [rowValid,hn]
    | some dest =>
      have ht : (table rows q false).next = some dest := by
        rw [table_in_range rows q hq false]
        simpa [he] using hn
      have h := hclosed q hq false dest ht
      simp [rowValid,hn,h]
  · cases hn : pair.2.next with
    | none => simp [rowValid,hn]
    | some dest =>
      have ht : (table rows q true).next = some dest := by
        rw [table_in_range rows q hq true]
        simpa [he] using hn
      have h := hclosed q hq true dest ht
      simp [rowValid,hn,h]

/-- The polynomially constructed finite adapter passes the actual Boolean
validity check whenever the original nonempty finite table does. -/
theorem adapt_valid (original : EncRows) (hn : 0 < original.length)
    (hv : valid (decodeRows original) = true) :
    valid (decodeRows (Source284EmptyBranchFinite.adapt original)) = true := by
  apply valid_of_closed
  simpa using Source284EmptyBranchFinite.adapt_closed original hn hv

/-- With the zero tail, the actual unary-record source numeral for the
adapter has a quadratic bit-length bound in its number of logical states.
This is a description-size bound, not a physical beeper-state count. -/
theorem adapt_source_size (original : EncRows) (hn : 0 < original.length)
    (hv : valid (decodeRows original) = true) :
    Nat.size (Source284ListTables.source (decodeRows (Source284EmptyBranchFinite.adapt original))) ≤
      1 + 2*(original.length+2)*(8*(original.length+2)+8) := by
  have h := Source284ListTables.source_size (decodeRows (Source284EmptyBranchFinite.adapt original))
    (adapt_valid original hn hv)
  simpa [Source284EmptyBranchFinite.adapt_length] using h

end Shared.Beeping.NPcoNP.Source284EmptyBranchValidity
