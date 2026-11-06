import Shared.Beeping.NPcoNP.Source284EncodedRecordList
import Shared.ComplexityBridge.TM2GateCNFPieces
import Shared.ComplexityBridge.TM2FlattenList

/-! Binary source-record code generation from the explicit finite relative
row list. Only bounded binary operations occur here; no row is expanded into
a unary record at this stage. -/
namespace Shared.Beeping.NPcoNP.Source284EncodedRecordListTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284EncodedRowCodeTM2
open Shared.Beeping.NPcoNP.Source284EncodedRecordList

def pairCodes (p : EncRow × EncRow) : List Nat := [code p.1,code p.2]

theorem pairCodes_isPolyTime : IsPolyTime pairCodes := by
  let a : EncRow × EncRow → Nat := fun p => code p.1
  let b : EncRow × EncRow → Nat := fun p => code p.2
  have ha : IsPolyTime a := TM2Compose.isPolyTime_comp (fun p : EncRow × EncRow => p.1)
    code TM2PairFirst.first_isPolyTime code_isPolyTime
  have hb : IsPolyTime b := TM2Compose.isPolyTime_comp (fun p : EncRow × EncRow => p.2)
    code TM2GuardAllStep.second_isPolyTime code_isPolyTime
  have h := TM2GateCNFPieces.pairList_isPolyTime a b ha hb
  change IsPolyTime (fun p : EncRow × EncRow => [code p.1,code p.2])
  simpa [a,b] using h

theorem recordsList_isPolyTime : IsPolyTime recordsList := by
  have hm := TM2ContextMapGeneric.listMap_isPolyTime pairCodes pairCodes_isPolyTime
  have h := TM2Compose.isPolyTime_comp (fun rows : EncRows => rows.map pairCodes)
    (List.flatten : List (List Nat) → List Nat) hm TM2FlattenList.flatten_isPolyTime
  change IsPolyTime (fun rows : EncRows => (rows.map pairCodes).flatten)
  exact h

end Shared.Beeping.NPcoNP.Source284EncodedRecordListTM2
