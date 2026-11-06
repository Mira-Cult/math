import Shared.Beeping.NPcoNP.Source284HardwireIndexedPairTM2
import Shared.Beeping.NPcoNP.Source284HardwireIndexedTurnsTM2
import Shared.ComplexityBridge.TM2IndexedMapLoop
import Shared.ComplexityBridge.TM2BinaryListLength
import Shared.ComplexityBridge.TM2EmptyConstant
import Shared.ComplexityBridge.TM2FixedRows

set_option backward.isDefEq.respectTransparency false

/-! A canonical polynomial-time machine generating the complete fixed-input
loader prefix. Both index traversals are over the actual input list; their
starting indices are finite binary values computed from that list. -/
namespace Shared.Beeping.NPcoNP.Source284HardwireIndexedPrefixTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2IndexedMap
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284HardwireIndexedList
open Shared.Beeping.NPcoNP.Source284HardwireIndexedPairTM2
open Shared.Beeping.NPcoNP.Source284HardwireIndexedTurnsTM2

private theorem append_isPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f g : α → List β) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => f x ++ g x) := by
  have hp := TM2GuardAllStep.pair_isPolyTime f g hf hg
  have h := TM2Compose.isPolyTime_comp (fun x => (f x,g x))
    (TM2ListAppend.append (α := β)) hp TM2ListAppend.append_isPolyTime
  simpa [TM2ListAppend.append] using h

theorem loaderPrefix_isPolyTime : IsPolyTime loaderPrefix := by
  let idBits : List Bool → List Bool := id
  let zero : List Bool → Nat := fun _ => 0
  let start : List Bool → Nat := fun bits => bits.length+1
  let write : List Bool → EncRows := fun bits => indexed writePair 0 bits
  let rewind : List Bool → EncRows := fun bits => indexed rewindPair (start bits) bits
  have hi : IsPolyTime idBits := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hz : IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have hl : IsPolyTime (List.length : List Bool → Nat) := TM2BinaryListLength.length_isPolyTime
  have hs : IsPolyTime start := TM2Compose.isPolyTime_comp (List.length : List Bool → Nat)
    (fun n : Nat => n+1) hl (TM2FixedRows.addFixed_isPolyTime 1)
  have hw : IsPolyTime write := TM2Compose.isPolyTime_comp (fun bits => (zero bits,idBits bits))
    (fun p : Nat × List Bool => indexed writePair p.1 p.2)
    (TM2GuardAllStep.pair_isPolyTime zero idBits hz hi)
    (TM2IndexedMapLoop.indexed_isPolyTime writePair writePair_isPolyTime)
  have hr : IsPolyTime rewind := TM2Compose.isPolyTime_comp (fun bits => (start bits,idBits bits))
    (fun p : Nat × List Bool => indexed rewindPair p.1 p.2)
    (TM2GuardAllStep.pair_isPolyTime start idBits hs hi)
    (TM2IndexedMapLoop.indexed_isPolyTime rewindPair rewindPair_isPolyTime)
  have h := append_isPolyTime write _ hw
    (append_isPolyTime _ _ turnOne_isPolyTime
      (append_isPolyTime rewind _ hr turnLast_isPolyTime))
  change IsPolyTime (fun bits : List Bool => indexed writePair 0 bits ++
    [((false,true,true,bits.length+1),(false,true,true,bits.length+1))] ++
    indexed rewindPair (bits.length+1) bits ++
    [((false,true,true,Shared.Beeping.NPcoNP.Source284HardwireTable.offset bits),
      (true,true,true,Shared.Beeping.NPcoNP.Source284HardwireTable.offset bits))])
  simpa [write, rewind, start, zero, idBits, turnOne, turnLast] using h

end Shared.Beeping.NPcoNP.Source284HardwireIndexedPrefixTM2
