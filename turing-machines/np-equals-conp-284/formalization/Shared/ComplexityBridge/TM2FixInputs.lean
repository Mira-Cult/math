import Shared.ComplexityBridge.TM2InputBitLookup
import Shared.ComplexityBridge.TM2ShapeClauses

/-! Construct the actual fixed-input unit clauses in canonical polynomial
time, including indexed bit lookup and binary-index addition. -/
namespace Shared.ComplexityBridge.TM2FixInputs
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CNF

/-- One unit clause for an indexed input bit. -/
def item (p : (Nat × List Bool) × Nat) : Clause :=
  [(p.1.1+p.2,TM2InputBitLookup.lookup (p.1.2,p.2))]

theorem item_isPolyTime : ComplexityTheory.IsPolyTime item := by
  let context : (Nat × List Bool) × Nat → Nat × List Bool := fun p => p.1
  let idx : (Nat × List Bool) × Nat → Nat := fun p => p.2
  let base0 : Nat × List Bool → Nat := fun p => p.1
  let bits0 : Nat × List Bool → List Bool := fun p => p.2
  let base : (Nat × List Bool) × Nat → Nat := fun p => base0 (context p)
  let bits : (Nat × List Bool) × Nat → List Bool := fun p => bits0 (context p)
  let addargs : (Nat × List Bool) × Nat → Nat × Nat := fun p => (base p,idx p)
  let bitargs : (Nat × List Bool) × Nat → List Bool × Nat := fun p => (bits p,idx p)
  let pos : (Nat × List Bool) × Nat → Nat := fun p => CNFBinaryPairAdd.addPair (addargs p)
  let value : (Nat × List Bool) × Nat → Bool := fun p => TM2InputBitLookup.lookup (bitargs p)
  let lit : (Nat × List Bool) × Nat → Literal := fun p => (pos p,value p)
  let empty : (Nat × List Bool) × Nat → Clause := fun _ => []
  let req : (Nat × List Bool) × Nat → Literal × Clause := fun p => (lit p,empty p)
  have hc : ComplexityTheory.IsPolyTime context := TM2PairFirst.first_isPolyTime
  have hi : ComplexityTheory.IsPolyTime idx := TM2GuardAllStep.second_isPolyTime
  have hb0 : ComplexityTheory.IsPolyTime base0 := TM2PairFirst.first_isPolyTime
  have ht0 : ComplexityTheory.IsPolyTime bits0 := TM2GuardAllStep.second_isPolyTime
  have hb : ComplexityTheory.IsPolyTime base := TM2Compose.isPolyTime_comp context base0 hc hb0
  have ht : ComplexityTheory.IsPolyTime bits := TM2Compose.isPolyTime_comp context bits0 hc ht0
  have hba : ComplexityTheory.IsPolyTime addargs := TM2GuardAllStep.pair_isPolyTime base idx hb hi
  have hta : ComplexityTheory.IsPolyTime bitargs := TM2GuardAllStep.pair_isPolyTime bits idx ht hi
  have hp : ComplexityTheory.IsPolyTime pos := TM2Compose.isPolyTime_comp addargs CNFBinaryPairAdd.addPair hba CNFBinaryPairAdd.addPair_isPolyTime
  have hv : ComplexityTheory.IsPolyTime value := TM2Compose.isPolyTime_comp bitargs TM2InputBitLookup.lookup hta TM2InputBitLookup.lookup_isPolyTime
  have hl : ComplexityTheory.IsPolyTime lit := TM2GuardAllStep.pair_isPolyTime pos value hp hv
  have he : ComplexityTheory.IsPolyTime empty := TM2EmptyConstant.isPolyTime [] rfl
  have hr : ComplexityTheory.IsPolyTime req := TM2GuardAllStep.pair_isPolyTime lit empty hl he
  have h := TM2Compose.isPolyTime_comp req (TM2ListAppend.cons (α := Literal)) hr TM2ListAppend.cons_isPolyTime
  change ComplexityTheory.IsPolyTime (fun p : (Nat × List Bool) × Nat => [(p.1.1+p.2,TM2InputBitLookup.lookup (p.1.2,p.2))])
  simpa [req,lit,pos,value,addargs,bitargs,base,bits,base0,bits0,context,idx,empty,CNFBinaryPairAdd.addPair,TM2ListAppend.cons] using h

def construct (p : Nat × List Bool) : Formula :=
  (List.range p.2.length).map (fun i => item (p,i))

theorem construct_isPolyTime : ComplexityTheory.IsPolyTime construct := by
  let indices : Nat × List Bool → List Nat := fun p => TM2UnaryRange.rangeFromTokens p.2
  let args : Nat × List Bool → (Nat × List Bool) × List Nat := fun p => (p,indices p)
  have hs : ComplexityTheory.IsPolyTime (fun p : Nat × List Bool => p.2) := TM2GuardAllStep.second_isPolyTime
  have hi : ComplexityTheory.IsPolyTime indices := TM2Compose.isPolyTime_comp (fun p : Nat × List Bool => p.2) TM2UnaryRange.rangeFromTokens hs TM2UnaryRange.rangeFromTokens_isPolyTime
  have hid : ComplexityTheory.IsPolyTime (id : Nat × List Bool → Nat × List Bool) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime id indices hid hi
  have hm := TM2ContextMapGeneric.contextMap_isPolyTime item item_isPolyTime
  have h := TM2Compose.isPolyTime_comp args (TM2ContextMapGeneric.contextMap item) ha hm
  change ComplexityTheory.IsPolyTime (fun p : Nat × List Bool => (List.range p.2.length).map (fun i => item (p,i)))
  simpa [args,indices,TM2UnaryRange.rangeFromTokens,TM2ContextMapGeneric.contextMap] using h

theorem range_correct (bits : List Bool) (base : Nat) :
    (List.range bits.length).map (fun i => [(base+i,(bits[i]?).getD false)]) =
      CircuitCNF.fixInputs base bits := by
  induction bits generalizing base with
  | nil => rfl
  | cons b bits ih =>
    simp only [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,Function.comp_def,
      List.getElem?_cons_zero,Option.getD_some,List.getElem?_cons_succ,Nat.add_zero,CircuitCNF.fixInputs]
    congr 1
    have he : (fun i : Nat => [(base+(i+1),(bits[i]?).getD false)]) =
        (fun i => [(base+1+i,(bits[i]?).getD false)]) := by
      funext i
      congr 2; omega
    rw [he,ih]

theorem construct_correct (base : Nat) (bits : List Bool) :
    construct (base,bits) = CircuitCNF.fixInputs base bits := by
  simp only [construct,item,TM2InputBitLookup.lookup_correct]
  exact range_correct bits base

theorem fixInputs_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Nat × List Bool => CircuitCNF.fixInputs p.1 p.2) := by
  have h := construct_isPolyTime
  have he : construct = (fun p : Nat × List Bool => CircuitCNF.fixInputs p.1 p.2) := by
    funext p
    exact construct_correct p.1 p.2
  rw [he] at h
  exact h

namespace Fixtures
example : construct (9,[]) = [] := rfl
example : construct (9,[true,false]) = [[(9,true)],[(10,false)]] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2FixInputs
