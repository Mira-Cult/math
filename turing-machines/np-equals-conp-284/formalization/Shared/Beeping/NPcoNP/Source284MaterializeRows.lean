import Shared.Beeping.NPcoNP.Source284EncodedRows

/-! Materialize a finite relative table as explicit encoded rows. This is an
executable finite list construction and an extensional bridge; no uniform
polynomial running time is asserted for an arbitrary function-valued table. -/
namespace Shared.Beeping.NPcoNP.Source284MaterializeRows

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284EncodedRows

def rows (n : Nat) (t : Nat → Bool → Row) : EncRows :=
  encodeRows (List.ofFn (fun q : Fin n => (t q false,t q true)))

theorem rows_length (n : Nat) (t : Nat → Bool → Row) : (rows n t).length = n := by
  simp [rows]

theorem table_agrees (n : Nat) (t : Nat → Bool → Row) (q : Nat)
    (hq : q < n) (read : Bool) :
    Source284ListTables.table (decodeRows (rows n t)) q read = t q read := by
  rw [rows, decode_encode_rows, Source284ListTables.table_in_range]
  · cases read <;> simp
  · simpa using hq

theorem table_closed (n : Nat) (t : Nat → Bool → Row) (hc : Closed n t) :
    Closed (rows n t).length (Source284ListTables.table (decodeRows (rows n t))) := by
  intro q hq read q' hn
  have hq' : q < n := by simpa [rows_length] using hq
  rw [table_agrees n t q hq' read] at hn
  simpa [rows_length] using hc q hq' read q' hn

/-- Materialization preserves the entire encoded program numeral, including
the explicit high tail, since only the allocated rows are serialized. -/
theorem encode_agrees (n : Nat) (t : Nat → Bool → Row) (tail : Nat) :
    encode (rows n t).length (Source284ListTables.table (decodeRows (rows n t))) tail =
      encode n t tail := by
  have he : records n (Source284ListTables.table (decodeRows (rows n t))) =
      records n t := by
    apply List.ext_getElem
    · simp [records]
    · intro i h₁ h₂
      have hi : i / 2 < n := by simp only [records,List.length_ofFn] at h₂; omega
      simp only [records,List.getElem_ofFn]
      rw [table_agrees n t (i/2) hi]
  simp only [encode,rows_length,he]

end Shared.Beeping.NPcoNP.Source284MaterializeRows
