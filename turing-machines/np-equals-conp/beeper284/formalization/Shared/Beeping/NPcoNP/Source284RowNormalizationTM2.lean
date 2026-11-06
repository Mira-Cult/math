import Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2
import Shared.ComplexityBridge.TM2If
import Shared.ComplexityBridge.TM2ListLookup
import Shared.Beeping.NPcoNP.Source284ConstantEncodedRowsTM2

/-! Polynomial-time normalization of explicitly encoded rows. A terminal
row's destination is ignored semantically and is normalized to zero. -/
namespace Shared.Beeping.NPcoNP.Source284RowNormalizationTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2 (row_isPolyTime)

theorem normalizeRow_isPolyTime : IsPolyTime normalizeRow := by
  let write : EncRow → Bool := fun r => r.1
  let rest : EncRow → Bool × Bool × Nat := fun r => r.2
  let turn : EncRow → Bool := fun r => (rest r).1
  let last : EncRow → Bool × Nat := fun r => (rest r).2
  let continues : EncRow → Bool := fun r => (last r).1
  let dest : EncRow → Nat := fun r => (last r).2
  let zero : EncRow → Nat := fun _ => 0
  have hw : IsPolyTime write := TM2PairFirst.first_isPolyTime
  have hr : IsPolyTime rest := TM2GuardAllStep.second_isPolyTime
  have ht : IsPolyTime turn := TM2Compose.isPolyTime_comp rest
    (fun p : Bool × Bool × Nat => p.1) hr TM2PairFirst.first_isPolyTime
  have hl : IsPolyTime last := TM2Compose.isPolyTime_comp rest
    (fun p : Bool × Bool × Nat => p.2) hr TM2GuardAllStep.second_isPolyTime
  have hc : IsPolyTime continues := TM2Compose.isPolyTime_comp last
    (fun p : Bool × Nat => p.1) hl TM2PairFirst.first_isPolyTime
  have hd : IsPolyTime dest := TM2Compose.isPolyTime_comp last
    (fun p : Bool × Nat => p.2) hl TM2GuardAllStep.second_isPolyTime
  have hz : IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have hsel := TM2If.if_isPolyTime continues dest zero hc hd hz
  have h := row_isPolyTime write turn continues (fun r => if continues r then dest r else zero r)
    hw ht hc hsel
  change IsPolyTime (fun r : EncRow =>
    (r.1,r.2.1,r.2.2.1,if r.2.2.1 then r.2.2.2 else 0))
  simpa [write,rest,turn,last,continues,dest,zero] using h

theorem normalizePair_isPolyTime : IsPolyTime (fun p : EncRow × EncRow =>
    (normalizeRow p.1,normalizeRow p.2)) := by
  have h1 := TM2Compose.isPolyTime_comp (fun p : EncRow × EncRow => p.1)
    normalizeRow TM2PairFirst.first_isPolyTime normalizeRow_isPolyTime
  have h2 := TM2Compose.isPolyTime_comp (fun p : EncRow × EncRow => p.2)
    normalizeRow TM2GuardAllStep.second_isPolyTime normalizeRow_isPolyTime
  exact TM2GuardAllStep.pair_isPolyTime _ _ h1 h2

def fallback : EncRow × EncRow := ((false,false,false,0),(false,false,false,0))

/-- Total lookup is charged for the complete encoded row list and binary
index. The out-of-range default is the source table's accepting fallback. -/
def lookupPair (p : EncRows × Nat) : EncRow × EncRow :=
  let r := TM2ListLookup.lookup (p.1,(p.2,fallback))
  (normalizeRow r.1,normalizeRow r.2)

theorem lookupPair_isPolyTime : IsPolyTime lookupPair := by
  let rows : EncRows × Nat → EncRows := fun p => p.1
  let index : EncRows × Nat → Nat := fun p => p.2
  let deflt : EncRows × Nat → EncRow × EncRow := fun _ => fallback
  have hr : IsPolyTime rows := TM2PairFirst.first_isPolyTime
  have hi : IsPolyTime index := TM2GuardAllStep.second_isPolyTime
  have hd : IsPolyTime deflt := Source284ConstantEncodedRowsTM2.constPair_isPolyTime fallback
  have ha := TM2GuardAllStep.pair_isPolyTime rows (fun p => (index p,deflt p)) hr
    (TM2GuardAllStep.pair_isPolyTime index deflt hi hd)
  have hl := TM2Compose.isPolyTime_comp (fun p => (rows p,(index p,deflt p)))
    (TM2ListLookup.lookup (β := EncRow × EncRow)) ha TM2ListLookup.lookup_isPolyTime
  have h := TM2Compose.isPolyTime_comp
    (fun p : EncRows × Nat => TM2ListLookup.lookup (p.1,(p.2,fallback)))
    (fun p : EncRow × EncRow => (normalizeRow p.1,normalizeRow p.2)) hl normalizePair_isPolyTime
  exact h

theorem lookupPair_correct (rows : EncRows) (q : Nat) (read : Bool) :
    (if read then (lookupPair (rows,q)).2 else (lookupPair (rows,q)).1) =
      encodeRow (Source284ListTables.table (decodeRows rows) q read) := by
  cases h : rows[q]? with
  | none => cases read <;> simp [lookupPair,TM2ListLookup.lookup,h,decodeRows,
      Source284ListTables.table,Source284ListTables.fallback,fallback,normalizeRow,encodeRow]
  | some r => cases read <;> simp [lookupPair,TM2ListLookup.lookup,h,decodeRows,
      Source284ListTables.table,encode_decode_row]

/-- Relocation and re-encoding use the canonical terminal-row destination. -/
def normalizedShift (p : Nat × EncRow) : EncRow :=
  normalizeRow (Source284HardwireEncodedWorkersTM2.shiftEncoded p)

theorem normalizedShift_isPolyTime : IsPolyTime normalizedShift :=
  TM2Compose.isPolyTime_comp Source284HardwireEncodedWorkersTM2.shiftEncoded normalizeRow
    Source284HardwireEncodedWorkersTM2.shiftEncoded_isPolyTime normalizeRow_isPolyTime

theorem normalizedShift_correct (offset : Nat) (r : EncRow) :
    normalizedShift (offset,r) =
      encodeRow (Source284HardwireTable.shiftRow offset (decodeRow r)) := by
  rw [← Source284HardwireEncodedWorkersTM2.decode_shiftEncoded, encode_decode_row]
  rfl

end Shared.Beeping.NPcoNP.Source284RowNormalizationTM2
