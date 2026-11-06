import Shared.Beeping.NPcoNP.Source284EncodedRowCodeTM2
import Mathlib.Data.List.OfFn

/-! A structural finite-list presentation of the exact source record order.
This is an extensional identity for all encoded row lists, including invalid
or unreachable destinations. It makes no unary-serialization claim. -/
namespace Shared.Beeping.NPcoNP.Source284EncodedRecordList

open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284EncodedRowCodeTM2
open Shared.Beeping.NPcoNP.Source284TableEncode

def recordsList (rows : EncRows) : List Nat :=
  rows.flatMap (fun p => [code p.1,code p.2])

private theorem block (rows : EncRows) (q : Fin rows.length) :
    List.ofFn (fun j : Fin 2 => rowCode
      (Shared.Beeping.NPcoNP.Source284ListTables.table (decodeRows rows)
        ((2*q.val+j.val)/2) ((2*q.val+j.val)%2=1))) =
      [code rows[q.val].1,code rows[q.val].2] := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h : i < 2 := by simpa using hj
    interval_cases i
    · have hr := lookup rows q.val q.isLt false
      have hv := congrArg rowCode hr
      have hd : (2*q.val)/2 = q.val := by omega
      have hm : (2*q.val)%2 = 0 := by omega
      simpa [code, hd, hm] using hv
    · have hr := lookup rows q.val q.isLt true
      have hv := congrArg rowCode hr
      have hd : (2*q.val+1)/2 = q.val := by omega
      have hm : (2*q.val+1)%2 = 1 := by omega
      simpa [code, hd, hm] using hv

/-- Both read-symbol records of every concrete row pair are enumerated in
exactly the same order as the shared function-table record definition. -/
theorem recordsList_eq (rows : EncRows) : recordsList rows =
    records (decodeRows rows).length
      (Shared.Beeping.NPcoNP.Source284ListTables.table (decodeRows rows)) := by
  symm
  unfold records
  simp only [decodeRows_length]
  rw [List.ofFn_mul']
  change (List.ofFn fun q : Fin rows.length =>
      List.ofFn fun j : Fin 2 => rowCode
        (Shared.Beeping.NPcoNP.Source284ListTables.table (decodeRows rows)
          ((2*q.val+j.val)/2) ((2*q.val+j.val)%2=1))).flatten = recordsList rows
  have hchunks : (List.ofFn fun q : Fin rows.length =>
      List.ofFn fun j : Fin 2 => rowCode
        (Shared.Beeping.NPcoNP.Source284ListTables.table (decodeRows rows)
          ((2*q.val+j.val)/2) ((2*q.val+j.val)%2=1))) =
      rows.map (fun p => [code p.1,code p.2]) := by
    rw [← List.ofFn_getElem_eq_map rows (fun p => [code p.1,code p.2])]
    congr 1
    funext q
    exact block rows q
  rw [hchunks]
  simp [recordsList, List.flatMap]

end Shared.Beeping.NPcoNP.Source284EncodedRecordList
