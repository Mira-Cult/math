import Shared.ComplexityBridge.TM2IndexedMapLoop
import Shared.ComplexityBridge.TM2BoundedWitnessGuard
import Shared.ComplexityBridge.TM2FlattenList
import Shared.ComplexityBridge.TM2GateCNFPieces

set_option backward.isDefEq.respectTransparency false

/-! Total indexed lookup for arbitrary canonical element encodings. The
index is binary and is never expanded into unary tokens. -/
namespace Shared.ComplexityBridge.TM2ListLookup
open Shared.ComplexityBridge

variable {β : Type} [BitstringEncoding β]
abbrev Request (β : Type) := List β × (Nat × β)

def hit (p : Nat × (Nat × β)) : List β :=
  TM2ListMask.mask (!TM2BoundedWitnessGuard.numericNe (p.1,p.2.1),[p.2.2])

theorem hit_isPolyTime : ComplexityTheory.IsPolyTime (hit (β := β)) := by
  let index : Nat × (Nat × β) → Nat := fun p => p.1
  let rest : Nat × (Nat × β) → Nat × β := fun p => p.2
  let query : Nat × (Nat × β) → Nat := fun p => p.2.1
  let val : Nat × (Nat × β) → β := fun p => p.2.2
  let neq : Nat × (Nat × β) → Bool := fun p => TM2BoundedWitnessGuard.numericNe (index p,query p)
  let flag : Nat × (Nat × β) → Bool := fun p => !neq p
  let single : Nat × (Nat × β) → List β := fun p => [val p]
  have hi : ComplexityTheory.IsPolyTime index := TM2PairFirst.first_isPolyTime
  have hr : ComplexityTheory.IsPolyTime rest := TM2GuardAllStep.second_isPolyTime
  have hq : ComplexityTheory.IsPolyTime query := TM2Compose.isPolyTime_comp rest (fun p : Nat × β => p.1) hr TM2PairFirst.first_isPolyTime
  have hv : ComplexityTheory.IsPolyTime val := TM2Compose.isPolyTime_comp rest (fun p : Nat × β => p.2) hr TM2GuardAllStep.second_isPolyTime
  have hn : ComplexityTheory.IsPolyTime neq := TM2Compose.isPolyTime_comp (fun p => (index p,query p))
    TM2BoundedWitnessGuard.numericNe (TM2GuardAllStep.pair_isPolyTime index query hi hq) TM2BoundedWitnessGuard.numericNe_isPolyTime
  have hf : ComplexityTheory.IsPolyTime flag := TM2Compose.isPolyTime_comp neq (fun b => !b) hn TM2GateDispatch.not_isPolyTime
  have hs : ComplexityTheory.IsPolyTime single := TM2GateCNFPieces.singleton_isPolyTime val hv
  have h := TM2Compose.isPolyTime_comp (fun p => (flag p,single p)) (TM2ListMask.mask (α := β))
    (TM2GuardAllStep.pair_isPolyTime flag single hf hs) TM2ListMask.mask_isPolyTime
  change ComplexityTheory.IsPolyTime (hit (β := β)) at h
  exact h

def selection (start query : Nat) (xs : List β) : List β :=
  (TM2IndexedMap.indexed hit start (xs.map (fun x => (query,x)))).flatten

omit [BitstringEncoding β] in
theorem selection_nil (start query : Nat) : selection (β := β) start query [] = [] := rfl

omit [BitstringEncoding β] in
theorem selection_cons (start query : Nat) (x : β) (xs : List β) :
    selection start query (x::xs) = (if start = query then [x] else []) ++ selection (start+1) query xs := by
  simp [selection,TM2IndexedMap.indexed,hit,TM2ListMask.mask,TM2BoundedWitnessGuard.numericNe]

theorem selection_before (start query : Nat) (xs : List β) (h : query < start) :
    selection start query xs = [] := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    rw [selection_cons]
    simp only [if_neg (show start ≠ query by omega),List.nil_append]
    exact ih (start+1) (by omega)

theorem selection_correct (start query : Nat) (xs : List β) (h : start ≤ query) :
    selection start query xs = (xs[query-start]?).toList := by
  induction xs generalizing start with
  | nil => simp [selection,TM2IndexedMap.indexed]
  | cons x xs ih =>
    rw [selection_cons]
    by_cases he : start = query
    · subst query
      rw [if_pos rfl,selection_before (start+1) start xs (by omega)]
      simp
    · have hlt : start < query := by omega
      rw [if_neg he, List.nil_append,ih (start+1) (by omega)]
      have hd : query-start = (query-(start+1))+1 := by omega
      rw [hd]
      simp

def selected (p : Request β) : List β := selection 0 p.2.1 p.1

theorem selected_correct (p : Request β) : selected p = (p.1[p.2.1]?).toList := by
  simpa [selected] using selection_correct 0 p.2.1 p.1 (Nat.zero_le _)

theorem selected_isPolyTime : ComplexityTheory.IsPolyTime (selected (β := β)) := by
  let xs : Request β → List β := fun p => p.1
  let rest : Request β → Nat × β := fun p => p.2
  let query : Request β → Nat := fun p => p.2.1
  let tagged : Request β → List (Nat × β) := fun p => TM2ContextMapGeneric.contextMap id (query p,xs p)
  let zero : Request β → Nat := fun _ => 0
  let args : Request β → Nat × List (Nat × β) := fun p => (zero p,tagged p)
  let blocks : Request β → List (List β) := fun p => TM2IndexedMap.indexed hit (args p).1 (args p).2
  have hx : ComplexityTheory.IsPolyTime xs := TM2PairFirst.first_isPolyTime
  have hr : ComplexityTheory.IsPolyTime rest := TM2GuardAllStep.second_isPolyTime
  have hq : ComplexityTheory.IsPolyTime query := TM2Compose.isPolyTime_comp rest (fun p : Nat × β => p.1) hr TM2PairFirst.first_isPolyTime
  have hid : ComplexityTheory.IsPolyTime (id : Nat × β → Nat × β) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hm := TM2ContextMapGeneric.contextMap_isPolyTime (id : Nat × β → Nat × β) hid
  have htag : ComplexityTheory.IsPolyTime tagged := TM2Compose.isPolyTime_comp (fun p => (query p,xs p))
    (TM2ContextMapGeneric.contextMap id) (TM2GuardAllStep.pair_isPolyTime query xs hq hx) hm
  have hz : ComplexityTheory.IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime zero tagged hz htag
  have hb : ComplexityTheory.IsPolyTime blocks := TM2Compose.isPolyTime_comp args
    (fun p : Nat × List (Nat × β) => TM2IndexedMap.indexed hit p.1 p.2) ha
    (TM2IndexedMapLoop.indexed_isPolyTime hit hit_isPolyTime)
  have h := TM2Compose.isPolyTime_comp blocks (List.flatten : List (List β) → List β) hb TM2FlattenList.flatten_isPolyTime
  change ComplexityTheory.IsPolyTime (selected (β := β)) at h
  exact h

def withDefault (p : Request β) : List β := selected p ++ [p.2.2]
def resultPair (p : Request β) : β × List β := ((p.1[p.2.1]?).getD p.2.2,(withDefault p).tail)

theorem withDefault_bits (p : Request β) :
    BitstringEncoding.bitEncode (withDefault p) = BitstringEncoding.bitEncode (resultPair p) := by
  rw [withDefault,selected_correct]
  cases h : p.1[p.2.1]? with
  | none => simp [resultPair,withDefault,selected_correct,h,TM2MapSizeBounds.encode_cons] <;> rfl
  | some x => simp [resultPair,withDefault,selected_correct,h,TM2MapSizeBounds.encode_cons] <;> rfl

theorem withDefault_isPolyTime : ComplexityTheory.IsPolyTime (withDefault (β := β)) := by
  let rest : Request β → Nat × β := fun p => p.2
  let fallback : Request β → β := fun p => p.2.2
  let last : Request β → List β := fun p => [fallback p]
  have hr : ComplexityTheory.IsPolyTime rest := TM2GuardAllStep.second_isPolyTime
  have hf : ComplexityTheory.IsPolyTime fallback := TM2Compose.isPolyTime_comp rest (fun p : Nat × β => p.2) hr TM2GuardAllStep.second_isPolyTime
  have hl : ComplexityTheory.IsPolyTime last := TM2GateCNFPieces.singleton_isPolyTime fallback hf
  have hp := TM2GuardAllStep.pair_isPolyTime selected last selected_isPolyTime hl
  have h := TM2Compose.isPolyTime_comp (fun p => (selected p,last p)) (TM2ListAppend.append (α := β)) hp TM2ListAppend.append_isPolyTime
  change ComplexityTheory.IsPolyTime (withDefault (β := β)) at h
  exact h

theorem resultPair_isPolyTime : ComplexityTheory.IsPolyTime (resultPair (β := β)) := by
  obtain ⟨m⟩ := withDefault_isPolyTime (β := β)
  refine ⟨{ toTM2ComputableAux := m.toTM2ComputableAux, time := m.time, outputsFun := ?_ }⟩
  intro p
  have h := m.outputsFun p
  change Turing.TM2OutputsInTime m.tm
    ((BitstringEncoding.bitEncode p).map m.inputAlphabet.symm)
    (some ((BitstringEncoding.bitEncode (resultPair p)).map m.outputAlphabet.symm))
    (m.time.eval (BitstringEncoding.bitEncode p).length)
  rw [←withDefault_bits]
  exact h

def lookup (p : Request β) : β := (p.1[p.2.1]?).getD p.2.2

/-- The exact total lookup, including an arbitrary encoded default, is
computed in polynomial time in the complete encoded list, index and default. -/
theorem lookup_isPolyTime : ComplexityTheory.IsPolyTime (lookup (β := β)) := by
  have h := TM2Compose.isPolyTime_comp (resultPair (β := β)) (fun p : β × List β => p.1)
    resultPair_isPolyTime TM2PairFirst.first_isPolyTime
  change ComplexityTheory.IsPolyTime (lookup (β := β)) at h
  exact h

/-- The exact default-zero reference lookup used by circuit relocation. -/
theorem naturalGet_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : List Nat × Nat => (p.1[p.2]?).getD 0) := by
  let xs : List Nat × Nat → List Nat := fun p => p.1
  let index : List Nat × Nat → Nat := fun p => p.2
  let zero : List Nat × Nat → Nat := fun _ => 0
  let args : List Nat × Nat → Request Nat := fun p => (xs p,(index p,zero p))
  have hx : ComplexityTheory.IsPolyTime xs := TM2PairFirst.first_isPolyTime
  have hi : ComplexityTheory.IsPolyTime index := TM2GuardAllStep.second_isPolyTime
  have hz : ComplexityTheory.IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime xs
    (fun p => (index p,zero p)) hx (TM2GuardAllStep.pair_isPolyTime index zero hi hz)
  have h := TM2Compose.isPolyTime_comp args (lookup (β := Nat)) ha lookup_isPolyTime
  change ComplexityTheory.IsPolyTime (fun p : List Nat × Nat => (p.1[p.2]?).getD 0) at h
  exact h

namespace Fixtures
example : lookup ([],(100,7)) = 7 := rfl
example : lookup ([3,5,7],(1,99)) = 5 := rfl
example : lookup ([3,5,7],(3,99)) = 99 := rfl
end Fixtures
end Shared.ComplexityBridge.TM2ListLookup
