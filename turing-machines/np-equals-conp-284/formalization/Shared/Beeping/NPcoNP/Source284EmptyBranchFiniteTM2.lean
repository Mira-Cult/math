import Shared.Beeping.NPcoNP.Source284EmptyBranchFinite
import Shared.Beeping.NPcoNP.Source284RowNormalizationTM2
import Shared.ComplexityBridge.TM2ContextMapGeneric
import Shared.ComplexityBridge.TM2ListAppend

/-! Polynomial construction of the explicit zero-prefix source adapter,
charged against the complete encoded finite row list. No verifier, timeout
guard, or physical beeper is constructed here. -/
namespace Shared.Beeping.NPcoNP.Source284EmptyBranchFiniteTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284EmptyBranchFinite
open Shared.Beeping.NPcoNP.Source284RowNormalizationTM2

abbrev Pair := EncRow × EncRow

def shiftPair (p : Pair) : Pair :=
  (normalizedShift (2,p.1),normalizedShift (2,p.2))

theorem shiftPair_isPolyTime : IsPolyTime shiftPair := by
  let two : Pair → Nat := fun _ => 2
  let first : Pair → EncRow := fun p => p.1
  let second : Pair → EncRow := fun p => p.2
  have hz : IsPolyTime (fun _ : Pair => (0 : Nat)) := TM2EmptyConstant.zero_isPolyTime
  have ht : IsPolyTime two := by
    have h := TM2Compose.isPolyTime_comp (fun _ : Pair => (0 : Nat))
      (fun n : Nat => n+2) hz (TM2FixedRows.addFixed_isPolyTime 2)
    simpa [two] using h
  have hf : IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hs : IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have ha := TM2Compose.isPolyTime_comp (fun p : Pair => (two p,first p)) normalizedShift
    (TM2GuardAllStep.pair_isPolyTime two first ht hf) normalizedShift_isPolyTime
  have hb := TM2Compose.isPolyTime_comp (fun p : Pair => (two p,second p)) normalizedShift
    (TM2GuardAllStep.pair_isPolyTime two second ht hs) normalizedShift_isPolyTime
  exact TM2GuardAllStep.pair_isPolyTime _ _ ha hb

def firstRow : Pair := ((false,false,false,0),(true,true,true,1))
def secondRow : Pair := ((false,true,true,2),(true,true,true,2))

def fast (rows : EncRows) : EncRows := firstRow :: secondRow :: rows.map shiftPair

theorem fast_isPolyTime : IsPolyTime fast := by
  let mapped : EncRows → EncRows := fun rows => rows.map shiftPair
  let one : EncRows → Pair := fun _ => firstRow
  let two : EncRows → Pair := fun _ => secondRow
  have hm : IsPolyTime mapped := TM2ContextMapGeneric.listMap_isPolyTime shiftPair shiftPair_isPolyTime
  have h1 : IsPolyTime one := Source284ConstantEncodedRowsTM2.constPair_isPolyTime firstRow
  have h2 : IsPolyTime two := Source284ConstantEncodedRowsTM2.constPair_isPolyTime secondRow
  have hp2 := TM2GuardAllStep.pair_isPolyTime two mapped h2 hm
  have hc2 := TM2Compose.isPolyTime_comp (fun rows : EncRows => (two rows,mapped rows))
    (TM2ListAppend.cons (α := Pair)) hp2 TM2ListAppend.cons_isPolyTime
  have hp1 := TM2GuardAllStep.pair_isPolyTime one (fun rows => two rows :: mapped rows) h1 (by
    simpa [TM2ListAppend.cons] using hc2)
  have hc1 := TM2Compose.isPolyTime_comp (fun rows : EncRows => (one rows,two rows :: mapped rows))
    (TM2ListAppend.cons (α := Pair)) hp1 TM2ListAppend.cons_isPolyTime
  change IsPolyTime (fun rows : EncRows => firstRow :: secondRow :: rows.map shiftPair)
  simpa [one,two,mapped,TM2ListAppend.cons] using hc1

theorem fast_eq_adapt : fast = adapt := by
  funext rows
  apply List.ext_getElem
  · simp [fast,adapt_length]
  · intro q hfast hadapt
    cases q with
    | zero =>
      simp [fast,firstRow,adapt,Source284MaterializeRows.rows,encodeRows,
        Source284EmptyBranchAdapter.table,encodeRow]
    | succ q =>
      cases q with
      | zero =>
        simp [fast,secondRow,adapt,Source284MaterializeRows.rows,encodeRows,
          Source284EmptyBranchAdapter.table,encodeRow]
      | succ q =>
        simp [fast,shiftPair,adapt,Source284MaterializeRows.rows,encodeRows,
          Source284EmptyBranchAdapter.table,Source284ListTables.table,
          decodeRows,normalizedShift_correct]

theorem adapt_isPolyTime : IsPolyTime adapt := by
  rw [← fast_eq_adapt]
  exact fast_isPolyTime

end Shared.Beeping.NPcoNP.Source284EmptyBranchFiniteTM2
