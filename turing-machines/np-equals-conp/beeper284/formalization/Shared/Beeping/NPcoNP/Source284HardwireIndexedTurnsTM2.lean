import Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2
import Shared.ComplexityBridge.TM2BinaryListLength
import Shared.ComplexityBridge.TM2GateCNFPieces
import Shared.ComplexityBridge.TM2FixedRows
import Shared.ComplexityBridge.TM2Constant
import Shared.ComplexityBridge.CNFBinaryIndex

set_option backward.isDefEq.respectTransparency false

/-! The two fixed paid turn rows in the hardwired-input loader. These
workers traverse only the actual input bit list and emit one pair of rows. -/
namespace Shared.Beeping.NPcoNP.Source284HardwireIndexedTurnsTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2

def turnOne (bits : List Bool) : EncRows :=
  [((false,true,true,bits.length+1), (false,true,true,bits.length+1))]

def turnLast (bits : List Bool) : EncRows :=
  [((false,true,true,offset bits), (true,true,true,offset bits))]

theorem lengthPlusOne_isPolyTime : IsPolyTime (fun bits : List Bool => bits.length+1) := by
  have h := TM2Compose.isPolyTime_comp (List.length : List Bool → Nat) (fun n : Nat => n+1)
    TM2BinaryListLength.length_isPolyTime (TM2FixedRows.addFixed_isPolyTime 1)
  exact h

theorem offset_isPolyTime : IsPolyTime offset := by
  have hdouble := TM2Compose.isPolyTime_comp (List.length : List Bool → Nat)
    (fun n : Nat => 2*n) TM2BinaryListLength.length_isPolyTime CNFBinaryIndex.double_isPolyTime
  have h := TM2Compose.isPolyTime_comp (fun bits : List Bool => 2*bits.length)
    (fun n : Nat => n+2) hdouble (TM2FixedRows.addFixed_isPolyTime 2)
  change IsPolyTime (fun bits : List Bool => 2*bits.length+2)
  exact h

private theorem turnRow_isPolyTime (write : Bool) (dest : List Bool → Nat) (hd : IsPolyTime dest) :
    IsPolyTime (fun bits => (write,true,true,dest bits) : List Bool → EncRow) := by
  exact row_isPolyTime (fun _ => write) (fun _ => true) (fun _ => true) dest
    (TM2Constant.isPolyTime write) (TM2Constant.isPolyTime true) (TM2Constant.isPolyTime true) hd

theorem turnOne_isPolyTime : IsPolyTime turnOne := by
  let row : List Bool → EncRow := fun bits => (false,true,true,bits.length+1)
  have hr : IsPolyTime row := turnRow_isPolyTime false (fun bits => bits.length+1) lengthPlusOne_isPolyTime
  have hp := TM2GuardAllStep.pair_isPolyTime row row hr hr
  have h := TM2GateCNFPieces.singleton_isPolyTime (fun bits => (row bits,row bits)) hp
  change IsPolyTime (fun bits : List Bool =>
    [((false,true,true,bits.length+1),(false,true,true,bits.length+1))])
  simpa [row] using h

theorem turnLast_isPolyTime : IsPolyTime turnLast := by
  let a : List Bool → EncRow := fun bits => (false,true,true,offset bits)
  let b : List Bool → EncRow := fun bits => (true,true,true,offset bits)
  have ha : IsPolyTime a := turnRow_isPolyTime false offset offset_isPolyTime
  have hb : IsPolyTime b := turnRow_isPolyTime true offset offset_isPolyTime
  have hp := TM2GuardAllStep.pair_isPolyTime a b ha hb
  have h := TM2GateCNFPieces.singleton_isPolyTime (fun bits => (a bits,b bits)) hp
  change IsPolyTime (fun bits : List Bool =>
    [((false,true,true,offset bits),(true,true,true,offset bits))])
  simpa [a,b] using h

end Shared.Beeping.NPcoNP.Source284HardwireIndexedTurnsTM2
