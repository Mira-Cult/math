import Shared.Beeping.NPcoNP.Source284HardwireIndexedList
import Shared.ComplexityBridge.TM2Constant
import Shared.ComplexityBridge.CNFBinaryIncrement

/-! Canonical polynomial-time workers for the two indexed loader traversals.
The index is a binary natural included in the input, and incrementing it is
charged by the binary successor machine. -/
namespace Shared.Beeping.NPcoNP.Source284HardwireIndexedPairTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2
open Shared.Beeping.NPcoNP.Source284HardwireIndexedList

abbrev Input := Nat × Bool

private theorem next_isPolyTime : IsPolyTime (fun p : Input => p.1 + 1) := by
  have h := TM2Compose.isPolyTime_comp (fun p : Input => p.1) Nat.succ
    TM2PairFirst.first_isPolyTime CNFBinaryIncrement.successor_isPolyTime
  simpa [Nat.succ_eq_add_one] using h

private theorem row (write : Input → Bool) (hw : IsPolyTime write) :
    IsPolyTime (fun p : Input => (write p,false,true,p.1+1) : Input → EncRow) :=
  row_isPolyTime write (fun _ => false) (fun _ => true) (fun p => p.1+1) hw
    (TM2Constant.isPolyTime false) (TM2Constant.isPolyTime true) next_isPolyTime

theorem writePair_isPolyTime : IsPolyTime writePair := by
  let r : Input → EncRow := fun p => (p.2,false,true,p.1+1)
  have hr : IsPolyTime r := row (fun p => p.2) TM2GuardAllStep.second_isPolyTime
  have h := TM2GuardAllStep.pair_isPolyTime r r hr hr
  change IsPolyTime (fun p : Input => ((p.2,false,true,p.1+1),(p.2,false,true,p.1+1)))
  simpa [r] using h

theorem rewindPair_isPolyTime : IsPolyTime rewindPair := by
  let f : Input → EncRow := fun p => (false,false,true,p.1+1)
  let t : Input → EncRow := fun p => (true,false,true,p.1+1)
  have hf : IsPolyTime f := row (fun _ => false) (TM2Constant.isPolyTime false)
  have ht : IsPolyTime t := row (fun _ => true) (TM2Constant.isPolyTime true)
  have h := TM2GuardAllStep.pair_isPolyTime f t hf ht
  change IsPolyTime (fun p : Input => ((false,false,true,p.1+1),(true,false,true,p.1+1)))
  simpa [f,t] using h

end Shared.Beeping.NPcoNP.Source284HardwireIndexedPairTM2
