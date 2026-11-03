import Shared.ComplexityBridge.TM2IndexedMapLoop
import Shared.ComplexityBridge.TM2GateConstruct
import Shared.ComplexityBridge.TM2ContextMapGeneric
import Shared.ComplexityBridge.TM2FlattenList

set_option backward.isDefEq.respectTransparency false

/-! Polynomial construction of the entire indexed mux sequence. -/
namespace Shared.ComplexityBridge.TM2MuxList
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitCNF

abbrev Context := Nat × Nat
abbrev Inputs := Nat × Nat
abbrev Item := Context × Inputs
abbrev Request := Context × List Inputs

def indexedMux (p : Nat × Item) : List Gate :=
  CircuitSelect.mux (p.2.1.1+4*p.1) p.2.1.2 p.2.2.1 p.2.2.2

theorem indexedMux_isPolyTime : ComplexityTheory.IsPolyTime indexedMux := by
  let index : Nat × Item → Nat := fun p => p.1
  let item : Nat × Item → Item := fun p => p.2
  let ctx : Nat × Item → Context := fun p => p.2.1
  let inputs : Nat × Item → Inputs := fun p => p.2.2
  let base : Nat × Item → Nat := fun p => p.2.1.1
  let selector : Nat × Item → Nat := fun p => p.2.1.2
  let twice : Nat × Item → Nat := fun p => 2*index p
  let four : Nat × Item → Nat := fun p => 2*twice p
  let offset : Nat × Item → Nat := fun p => base p+four p
  let rest : Nat × Item → Nat × Inputs := fun p => (selector p,inputs p)
  let args : Nat × Item → TM2GateConstruct.MuxInput := fun p => (offset p,rest p)
  have hi : ComplexityTheory.IsPolyTime index := TM2PairFirst.first_isPolyTime
  have hit : ComplexityTheory.IsPolyTime item := TM2GuardAllStep.second_isPolyTime
  have hc : ComplexityTheory.IsPolyTime ctx := TM2Compose.isPolyTime_comp item (fun p : Item => p.1) hit TM2PairFirst.first_isPolyTime
  have hp : ComplexityTheory.IsPolyTime inputs := TM2Compose.isPolyTime_comp item (fun p : Item => p.2) hit TM2GuardAllStep.second_isPolyTime
  have hb : ComplexityTheory.IsPolyTime base := TM2Compose.isPolyTime_comp ctx (fun p : Context => p.1) hc TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime selector := TM2Compose.isPolyTime_comp ctx (fun p : Context => p.2) hc TM2GuardAllStep.second_isPolyTime
  have ht : ComplexityTheory.IsPolyTime twice := TM2Compose.isPolyTime_comp index (fun n => 2*n) hi CNFBinaryIndex.double_isPolyTime
  have hf : ComplexityTheory.IsPolyTime four := TM2Compose.isPolyTime_comp twice (fun n => 2*n) ht CNFBinaryIndex.double_isPolyTime
  have ho : ComplexityTheory.IsPolyTime offset := TM2Compose.isPolyTime_comp (fun p => (base p,four p)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime base four hb hf) CNFBinaryPairAdd.addPair_isPolyTime
  have hr : ComplexityTheory.IsPolyTime rest := TM2GuardAllStep.pair_isPolyTime selector inputs hs hp
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime offset rest ho hr
  have h := TM2Compose.isPolyTime_comp args TM2GateConstruct.mux ha TM2GateConstruct.mux_isPolyTime
  have heq : (fun p => TM2GateConstruct.mux (args p)) = indexedMux := by
    funext p
    simp only [args,offset,rest,base,four,twice,index,selector,inputs,TM2GateConstruct.mux,indexedMux]
    congr 1 <;> omega
  rw [heq] at h
  exact h

def mapped (ctx : Context) (xs : List Inputs) : List Item := xs.map (fun x => (ctx,x))

theorem indexed_correct (base selector i : Nat) (xs : List Inputs) :
    (TM2IndexedMap.indexed indexedMux i (mapped (base,selector) xs)).flatten =
      CircuitSelect.muxes (base+4*i) selector xs := by
  induction xs generalizing i with
  | nil => simp [mapped,TM2IndexedMap.indexed,CircuitSelect.muxes]
  | cons x xs ih =>
    rcases x with ⟨yes,no⟩
    simp only [mapped,List.map_cons,TM2IndexedMap.indexed,List.flatten_cons,indexedMux,CircuitSelect.muxes]
    have htail := ih (i+1)
    have he : base+4*(i+1) = base+4*i+4 := by omega
    rw [he] at htail
    simpa [mapped] using congrArg (fun z => CircuitSelect.mux (base+4*i) selector yes no ++ z) htail

def muxList (p : Request) : List Gate := CircuitSelect.muxes p.1.1 p.1.2 p.2

/-- The finite machine constructs every mux and charges the entire input,
including the binary base, selector, and every input-pair encoding. -/
theorem muxList_isPolyTime : ComplexityTheory.IsPolyTime muxList := by
  let dup : Context × Inputs → Item := id
  let expand : Request → List Item := TM2ContextMapGeneric.contextMap dup
  let zero : Request → Nat := fun _ => 0
  let request : Request → Nat × List Item := fun p => (zero p,expand p)
  let blocks : Request → List (List Gate) := fun p => TM2IndexedMap.indexed indexedMux (request p).1 (request p).2
  have hd : ComplexityTheory.IsPolyTime dup := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have he : ComplexityTheory.IsPolyTime expand := TM2ContextMapGeneric.contextMap_isPolyTime dup hd
  have hz : ComplexityTheory.IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have hr : ComplexityTheory.IsPolyTime request := TM2GuardAllStep.pair_isPolyTime zero expand hz he
  have hi := TM2IndexedMapLoop.indexed_isPolyTime indexedMux indexedMux_isPolyTime
  have hb : ComplexityTheory.IsPolyTime blocks := TM2Compose.isPolyTime_comp request
    (fun p : Nat × List Item => TM2IndexedMap.indexed indexedMux p.1 p.2) hr hi
  have h := TM2Compose.isPolyTime_comp blocks (List.flatten : List (List Gate) → List Gate) hb TM2FlattenList.flatten_isPolyTime
  have heq : (fun p => (blocks p).flatten) = muxList := by
    funext p
    rcases p with ⟨⟨base,selector⟩,xs⟩
    simpa [blocks,request,zero,expand,dup,TM2ContextMapGeneric.contextMap,mapped,muxList] using indexed_correct base selector 0 xs
  rw [heq] at h
  exact h

namespace Fixtures
example : muxList ((5,1),[]) = [] := rfl
example : muxList ((5,1),[(2,3),(4,6)]) =
    [.neg 1,.conj 1 2,.conj 5 3,.disj 6 7,
     .neg 1,.conj 1 4,.conj 9 6,.disj 10 11] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2MuxList
