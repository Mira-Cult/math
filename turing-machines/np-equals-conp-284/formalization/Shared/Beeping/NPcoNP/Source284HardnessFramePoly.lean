import Shared.Beeping.NPcoNP.Source284HardnessFrame
import Shared.ComplexityBridge.TM2ContextMapGeneric
import Shared.ComplexityBridge.TM2ListReverse
import Shared.ComplexityBridge.TM2FlattenList
import Shared.ComplexityBridge.TM2GateCNFPieces
import Shared.ComplexityBridge.TM2Constant
import Shared.ComplexityBridge.Encodings

set_option backward.isDefEq.respectTransparency false

/-! The source reference's frame wrapper can be produced in canonical
polynomial time when its padding is supplied in unary as an arbitrary list.
The machine constructions for map, reverse, flatten, append and fixed blocks
are those already proved against the pinned TM2 complexity definition. This
does not supply a SAT-to-source-program compiler or prove NP-hardness. -/

namespace Shared.Beeping.NPcoNP.Source284HardnessFramePoly

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284Parser
open Shared.Beeping.NPcoNP.Source284HardnessFrame

abbrev Input := List Bool × List Bool

def zeros (p : Input) : List Bool := p.2.map (fun _ => false)
def padded (p : Input) : List Bool := p.1 ++ zeros p
def payload (p : Input) : List Bool := (padded p).reverse
def blocks (xs : List Bool) : List Bool := (xs.map (fun b => [true,b])).flatten
def produce (p : Input) : List Bool := blocks (payload p) ++ [false]

/-- Add one separating zero in addition to the caller's unary padding.
The separator enables a uniform acceptance-preservation proof when the high
sentinel is introduced. -/
def produceSafe (p : Input) : List Bool := produce (p.1, false :: p.2)

/-- Padding is unary in the full input length; its bit values do not matter. -/
theorem zeros_eq (p : Input) : zeros p = List.replicate p.2.length false := by
  cases p with
  | mk code pad =>
    change pad.map (fun _ => false) = List.replicate pad.length false
    induction pad with
    | nil => rfl
    | cons b bs ih => simp [ih, List.replicate_succ]

theorem blocks_frame (xs : List Bool) : frameBits xs [] = blocks xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simpa [frameBits, blocks] using congrArg (fun ys => true :: b :: ys) ih

/-- The concrete polynomial-time construction is exactly the framing API,
including the terminating zero marker and all zero padding. -/
theorem produce_eq_input (p : Input) :
    produce p = input p.1 p.2.length := by
  unfold produce input payload padded
  rw [zeros_eq, blocks_frame]

theorem produce_length (p : Input) :
    (produce p).length = 2 * (p.1.length + p.2.length) + 1 := by
  rw [produce_eq_input, input_length]
  rfl

theorem produce_encoded_length (p : Input) :
    (BitstringEncoding.bitEncode (produce p)).length =
      3 * (2 * (p.1.length + p.2.length) + 1) := by
  rw [Shared.ComplexityBridge.bitstring_list_encoded_length, produce_length]

/-- Output serialization is linear in the canonical encoding of the full
input pair, including the unary padding field. -/
theorem produce_encoded_linear (p : Input) :
    (BitstringEncoding.bitEncode (produce p)).length ≤
      2 * (BitstringEncoding.bitEncode p).length + 1 := by
  cases p with
  | mk code pad =>
    rw [produce_encoded_length, Shared.ComplexityBridge.bitstring_pair_encoded_length]
    simp only [Prod.fst, Prod.snd]
    omega

/-- Uniform polynomial time in the canonical encoding of the entire pair,
including all unary padding cells, and with no oracle or hidden answer data. -/
theorem produce_isPolyTime : ComplexityTheory.IsPolyTime produce := by
  let zeroBit : Bool → Bool := fun _ => false
  let block : Bool → List Bool := fun b => [true,b]
  let marker : Input → List Bool := fun _ => [false]
  let first : Input → List Bool := fun p => p.1
  let second : Input → List Bool := fun p => p.2
  have hz : ComplexityTheory.IsPolyTime zeroBit := TM2Constant.isPolyTime false
  have hmz : ComplexityTheory.IsPolyTime (fun xs : List Bool => xs.map zeroBit) :=
    TM2ContextMapGeneric.listMap_isPolyTime zeroBit hz
  have hs : ComplexityTheory.IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have hzeros : ComplexityTheory.IsPolyTime zeros := by
    have h := TM2Compose.isPolyTime_comp second (fun xs : List Bool => xs.map zeroBit) hs hmz
    change ComplexityTheory.IsPolyTime (fun p : Input => p.2.map (fun _ => false))
    simpa only [second,zeroBit] using h
  have hf : ComplexityTheory.IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hpair := TM2GuardAllStep.pair_isPolyTime first zeros hf hzeros
  have hpadded : ComplexityTheory.IsPolyTime padded := by
    have h := TM2Compose.isPolyTime_comp (fun p : Input => (first p, zeros p))
      (TM2ListAppend.append (α := Bool)) hpair TM2ListAppend.append_isPolyTime
    change ComplexityTheory.IsPolyTime (fun p : Input => p.1 ++ zeros p)
    simpa only [first,TM2ListAppend.append] using h
  have hpayload : ComplexityTheory.IsPolyTime payload := by
    exact TM2Compose.isPolyTime_comp padded (List.reverse : List Bool → List Bool)
      hpadded TM2ListReverse.reverse_isPolyTime
  have htrue : ComplexityTheory.IsPolyTime (fun _ : Bool => true) := TM2Constant.isPolyTime true
  have hid : ComplexityTheory.IsPolyTime (id : Bool → Bool) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hb : ComplexityTheory.IsPolyTime block := by
    simpa [block] using TM2GateCNFPieces.pairList_isPolyTime (fun _ : Bool => true) id htrue hid
  have hmap : ComplexityTheory.IsPolyTime (fun xs : List Bool => xs.map block) :=
    TM2ContextMapGeneric.listMap_isPolyTime block hb
  have hblocks : ComplexityTheory.IsPolyTime blocks := by
    have h := TM2Compose.isPolyTime_comp (fun xs : List Bool => xs.map block)
      (List.flatten : List (List Bool) → List Bool) hmap TM2FlattenList.flatten_isPolyTime
    change ComplexityTheory.IsPolyTime (fun xs : List Bool => (xs.map (fun b => [true,b])).flatten)
    simpa only [block] using h
  have hbody : ComplexityTheory.IsPolyTime (fun p : Input => blocks (payload p)) :=
    TM2Compose.isPolyTime_comp payload blocks hpayload hblocks
  have hm : ComplexityTheory.IsPolyTime marker := by
    have hfalse : ComplexityTheory.IsPolyTime (fun _ : Input => false) := TM2Constant.isPolyTime false
    simpa [marker] using TM2GateCNFPieces.singleton_isPolyTime (fun _ : Input => false) hfalse
  have hargs := TM2GuardAllStep.pair_isPolyTime (fun p : Input => blocks (payload p)) marker hbody hm
  have hout := TM2Compose.isPolyTime_comp (fun p : Input => (blocks (payload p),marker p))
    (TM2ListAppend.append (α := Bool)) hargs TM2ListAppend.append_isPolyTime
  change ComplexityTheory.IsPolyTime (fun p : Input => blocks (payload p) ++ [false])
  simpa only [marker,TM2ListAppend.append] using hout

theorem produceSafe_eq_input (p : Input) :
    produceSafe p = input p.1 (p.2.length + 1) := by
  simp [produceSafe, produce_eq_input]

/-- This bound includes the mandatory separator and the terminating marker. -/
theorem produceSafe_encoded_linear (p : Input) :
    (BitstringEncoding.bitEncode (produceSafe p)).length ≤
      2 * (BitstringEncoding.bitEncode p).length + 7 := by
  cases p with
  | mk code pad =>
    rw [Shared.ComplexityBridge.bitstring_list_encoded_length, produceSafe_eq_input,
      input_length, Shared.ComplexityBridge.bitstring_pair_encoded_length]
    simp only [clock, Prod.fst, Prod.snd]
    omega

theorem produceSafe_isPolyTime : ComplexityTheory.IsPolyTime produceSafe := by
  let first : Input → List Bool := fun p => p.1
  let second : Input → List Bool := fun p => p.2
  let pad : Input → List Bool := fun p => false :: second p
  have hf : ComplexityTheory.IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have hb : ComplexityTheory.IsPolyTime (fun _ : Input => false) := TM2Constant.isPolyTime false
  have hp : ComplexityTheory.IsPolyTime pad := by
    have harg := TM2GuardAllStep.pair_isPolyTime (fun _ : Input => false) second hb hs
    have h := TM2Compose.isPolyTime_comp (fun p : Input => (false,second p))
      (TM2ListAppend.cons (α := Bool)) harg TM2ListAppend.cons_isPolyTime
    simpa [pad, TM2ListAppend.cons] using h
  have harg := TM2GuardAllStep.pair_isPolyTime first pad hf hp
  have h := TM2Compose.isPolyTime_comp (fun p : Input => (first p,pad p)) produce harg produce_isPolyTime
  change ComplexityTheory.IsPolyTime (fun p : Input => produce (p.1, false :: p.2))
  simpa only [first, second, pad] using h

end Shared.Beeping.NPcoNP.Source284HardnessFramePoly
