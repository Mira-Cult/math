import Shared.Beeping.NPcoNP.Source284CompileRecordsList
import Shared.Beeping.NPcoNP.Source284CompileRowTM2
import Shared.ComplexityBridge.TM2BinaryListLength
import Shared.ComplexityBridge.TM2ContextMapGeneric
import Shared.ComplexityBridge.TM2FlattenList
import Shared.ComplexityBridge.TM2GateCNFPieces
import Shared.ComplexityBridge.TM2ListAppend

/-! Uniform canonical-TM2 construction of the existing finite-program
record list. The input is the existing finite tuple-list `Program`, not an
arbitrary function-valued table. This is binary-Nat record generation only:
unary source serialization and correctness for invalid continuations are
separate obligations. -/
namespace Shared.Beeping.NPcoNP.Source284CompileRecordsTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284CompileRecords
open Shared.Beeping.NPcoNP.Source284CompileRecordsList
open Shared.Beeping.NPcoNP.Source284CompileRowTM2

abbrev BlockInput := Nat × (Row × Row)

/-- Fixed four-element list output, with all element constructions charged. -/
theorem four_isPolyTime {α : Type} [BitstringEncoding α]
    (f g h k : α → Nat) (hf : IsPolyTime f) (hg : IsPolyTime g)
    (hh : IsPolyTime h) (hk : IsPolyTime k) :
    IsPolyTime (fun x => [f x,g x,h x,k x]) := by
  let tail : α → List Nat := fun x => [g x,h x,k x]
  have ht : IsPolyTime tail := TM2GateCNFPieces.tripleList_isPolyTime g h k hg hh hk
  have hp := TM2GuardAllStep.pair_isPolyTime f tail hf ht
  have hc := TM2Compose.isPolyTime_comp (fun x => (f x,tail x))
    (TM2ListAppend.cons (α := Nat)) hp TM2ListAppend.cons_isPolyTime
  simpa [tail, TM2ListAppend.cons] using hc

def rowAt (rev read : Bool) (p : BlockInput) : Nat :=
  encodedRow p.1 rev (if read then p.2.2 else p.2.1)

theorem rowAt_isPolyTime (rev read : Bool) : IsPolyTime (rowAt rev read) := by
  let size : BlockInput → Nat := fun p => p.1
  let orient : BlockInput → Bool := fun _ => rev
  let pair : BlockInput → Row × Row := fun p => p.2
  let row : BlockInput → Row := fun p => if read then p.2.2 else p.2.1
  have hs : IsPolyTime size := TM2PairFirst.first_isPolyTime
  have ho : IsPolyTime orient := TM2Constant.isPolyTime rev
  have hp : IsPolyTime pair := TM2GuardAllStep.second_isPolyTime
  have hr : IsPolyTime row := by
    cases read with
    | false =>
      simpa [row,pair] using TM2Compose.isPolyTime_comp pair
        (fun r : Row × Row => r.1) hp TM2PairFirst.first_isPolyTime
    | true =>
      simpa [row,pair] using TM2Compose.isPolyTime_comp pair
        (fun r : Row × Row => r.2) hp TM2GuardAllStep.second_isPolyTime
  have hso := TM2GuardAllStep.pair_isPolyTime size orient hs ho
  have hargs := TM2GuardAllStep.pair_isPolyTime (fun p => (size p,orient p)) row hso hr
  have he := TM2Compose.isPolyTime_comp (fun p : BlockInput => ((size p,orient p),row p))
    (fun p : (Nat × Bool) × Row => encodedRow p.1.1 p.1.2 p.2)
    hargs encodedRow_isPolyTime
  change IsPolyTime (fun p : BlockInput =>
    encodedRow p.1 rev (if read then p.2.2 else p.2.1))
  simpa [size,orient,row] using he

theorem rowBlock_isPolyTime : IsPolyTime (fun p : BlockInput => rowBlock p.1 p.2) := by
  simpa [rowBlock,rowAt] using
    four_isPolyTime (rowAt false false) (rowAt false true) (rowAt true false) (rowAt true true)
      (rowAt_isPolyTime false false) (rowAt_isPolyTime false true)
      (rowAt_isPolyTime true false) (rowAt_isPolyTime true true)

def sinkAt (rev read : Bool) (n : Nat) : Nat := pack read rev (rejectState n)

theorem sinkAt_isPolyTime (rev read : Bool) : IsPolyTime (sinkAt rev read) := by
  let wr : Nat → Bool := fun _ => read
  let tr : Nat → Bool := fun _ => rev
  have hw : IsPolyTime wr := TM2Constant.isPolyTime read
  have ht : IsPolyTime tr := TM2Constant.isPolyTime rev
  have hp := TM2GuardAllStep.pair_isPolyTime tr rejectState ht rejectState_isPolyTime
  have hargs := TM2GuardAllStep.pair_isPolyTime wr (fun n => (tr n,rejectState n)) hw hp
  have h := TM2Compose.isPolyTime_comp (fun n => (wr n,(tr n,rejectState n)))
    (fun z : Bool × Bool × Nat => pack z.1 z.2.1 z.2.2) hargs pack_isPolyTime
  change IsPolyTime (fun n : Nat => pack read rev (rejectState n))
  simpa [wr,tr] using h

theorem sinkBlock_isPolyTime : IsPolyTime sinkBlock := by
  change IsPolyTime (fun n : Nat =>
    [pack false false (rejectState n), pack true false (rejectState n),
      pack false true (rejectState n), pack true true (rejectState n)])
  simpa [sinkAt] using
    four_isPolyTime (sinkAt false false) (sinkAt false true) (sinkAt true false) (sinkAt true true)
      (sinkAt_isPolyTime false false) (sinkAt_isPolyTime false true)
      (sinkAt_isPolyTime true false) (sinkAt_isPolyTime true true)

/-- Map the polynomial row compiler over every actual input row, then append
the four sink rows. The table is an explicit finite input, with no function
reification or unbounded natural-number unit cost. -/
theorem recordsList_isPolyTime : IsPolyTime recordsList := by
  let size : Program → Nat := List.length
  let ident : Program → Program := id
  let args : Program → Nat × Program := fun p => (size p,ident p)
  let blocks : Program → List (List Nat) := fun p =>
    TM2ContextMapGeneric.contextMap (fun z : BlockInput => rowBlock z.1 z.2) (args p)
  let flat : Program → List Nat := fun p => (blocks p).flatten
  let sink : Program → List Nat := fun p => sinkBlock (size p)
  have hs : IsPolyTime size := TM2BinaryListLength.length_isPolyTime
  have hi : IsPolyTime ident := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have ha : IsPolyTime args := TM2GuardAllStep.pair_isPolyTime size ident hs hi
  have hb : IsPolyTime blocks := TM2Compose.isPolyTime_comp args
    (TM2ContextMapGeneric.contextMap (fun z : BlockInput => rowBlock z.1 z.2)) ha
      (TM2ContextMapGeneric.contextMap_isPolyTime _ rowBlock_isPolyTime)
  have hf : IsPolyTime flat := TM2Compose.isPolyTime_comp blocks
    (List.flatten : List (List Nat) → List Nat) hb TM2FlattenList.flatten_isPolyTime
  have hsin : IsPolyTime sink := TM2Compose.isPolyTime_comp size sinkBlock hs sinkBlock_isPolyTime
  have hpair := TM2GuardAllStep.pair_isPolyTime flat sink hf hsin
  have h := TM2Compose.isPolyTime_comp (fun p : Program => (flat p,sink p))
    (TM2ListAppend.append (α := Nat)) hpair TM2ListAppend.append_isPolyTime
  change IsPolyTime (fun p : Program =>
    (p.map (rowBlock p.length)).flatten ++ sinkBlock p.length)
  simpa [flat,blocks,args,size,ident,sink,TM2ContextMapGeneric.contextMap,
    TM2ListAppend.append] using h

/-- The exact preexisting source record compiler is canonically polynomial
time on explicit finite programs, without requiring validity. -/
theorem records_isPolyTime : IsPolyTime records := by
  have h : records = recordsList := funext records_eq_recordsList
  rw [h]
  exact recordsList_isPolyTime

end Shared.Beeping.NPcoNP.Source284CompileRecordsTM2
