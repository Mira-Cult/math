import Shared.Beeping.NPcoNP.Source284HardwireIndexedPrefixTM2
import Shared.ComplexityBridge.TM2ContextMapGeneric
import Shared.ComplexityBridge.TM2BinaryListLength
import Shared.ComplexityBridge.TM2FixedRows
import Shared.ComplexityBridge.CNFBinaryIndex

set_option backward.isDefEq.respectTransparency false

/-! Uniform construction of the fixed-input loader and relocated finite
relative table. The cost includes traversing the actual input bit list and
all supplied finite table rows, with binary arithmetic on destinations. -/
namespace Shared.Beeping.NPcoNP.Source284HardwireIndexedTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284HardwireIndexedList
open Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2
open Shared.Beeping.NPcoNP.Source284HardwireIndexedPrefixTM2

theorem offset_isPolyTime : IsPolyTime offset := by
  have hlen : IsPolyTime (List.length : List Bool → Nat) := TM2BinaryListLength.length_isPolyTime
  have hdouble := TM2Compose.isPolyTime_comp (List.length : List Bool → Nat) (fun n : Nat => 2*n)
    hlen CNFBinaryIndex.double_isPolyTime
  have h := TM2Compose.isPolyTime_comp (fun xs : List Bool => 2*xs.length) (fun n : Nat => n+2)
    hdouble (TM2FixedRows.addFixed_isPolyTime 2)
  change IsPolyTime (fun xs : List Bool => 2*xs.length+2)
  exact h

/-- A single finite TM2 constructs the entire relative-table list. -/
theorem rows_isPolyTime : IsPolyTime (fun p : List Bool × EncRows => rows p.1 p.2) := by
  let bits : List Bool × EncRows → List Bool := fun p => p.1
  let original : List Bool × EncRows → EncRows := fun p => p.2
  let n : List Bool × EncRows → Nat := fun p => offset (bits p)
  let pref : List Bool × EncRows → EncRows := fun p => loaderPrefix (bits p)
  let args : List Bool × EncRows → Nat × EncRows := fun p => (n p,original p)
  let shifted : List Bool × EncRows → EncRows := fun p => TM2ContextMapGeneric.contextMap shiftPair (args p)
  have hb : IsPolyTime bits := TM2PairFirst.first_isPolyTime
  have ho : IsPolyTime original := TM2GuardAllStep.second_isPolyTime
  have hn : IsPolyTime n := TM2Compose.isPolyTime_comp bits offset hb offset_isPolyTime
  have hp : IsPolyTime pref := TM2Compose.isPolyTime_comp bits loaderPrefix hb loaderPrefix_isPolyTime
  have ha : IsPolyTime args := TM2GuardAllStep.pair_isPolyTime n original hn ho
  have hs : IsPolyTime shifted := TM2Compose.isPolyTime_comp args
    (TM2ContextMapGeneric.contextMap shiftPair) ha
      (TM2ContextMapGeneric.contextMap_isPolyTime shiftPair shiftPair_isPolyTime)
  have h := TM2Compose.isPolyTime_comp (fun p => (pref p, shifted p))
    (TM2ListAppend.append (α := EncRow × EncRow))
    (TM2GuardAllStep.pair_isPolyTime pref shifted hp hs) TM2ListAppend.append_isPolyTime
  change IsPolyTime (fun p : List Bool × EncRows =>
    loaderPrefix p.1 ++ p.2.map (fun pair => shiftPair (offset p.1,pair)))
  simpa [pref,shifted,args,n,bits,original,TM2ContextMapGeneric.contextMap,
    TM2ListAppend.append] using h

end Shared.Beeping.NPcoNP.Source284HardwireIndexedTM2
