import Shared.ComplexityBridge.TM2BinaryListLength
import Shared.ComplexityBridge.TM2FlattenList

/-! Compute the product of two unary list lengths as a binary natural. The
finite context-map and flatten machines explicitly generate and charge every
intermediate token before the binary-length machine counts them. -/
namespace Shared.ComplexityBridge.TM2UnaryProductLength
open Shared.ComplexityBridge

def productBits (p : List Bool × List Bool) : List Bool :=
  (p.1.map (fun _ => p.2)).flatten

theorem productBits_length (a b : List Bool) :
    (productBits (a,b)).length = a.length*b.length := by
  induction a with
  | nil => simp [productBits]
  | cons x xs ih =>
    simp only [productBits,List.map_cons,List.flatten_cons,List.length_append,List.length_cons] at *
    rw [ih,Nat.add_mul]
    simp [Nat.add_comm]

theorem productBits_isPolyTime : ComplexityTheory.IsPolyTime productBits := by
  let swap : List Bool × List Bool → List Bool × List Bool := TM2PairSwap.swap
  let each : List Bool × Bool → List Bool := fun p => p.1
  let mapped : List Bool × List Bool → List (List Bool) := fun p => TM2ContextMapGeneric.contextMap each (swap p)
  have hs : ComplexityTheory.IsPolyTime swap := TM2PairSwap.swap_isPolyTime
  have he : ComplexityTheory.IsPolyTime each := TM2PairFirst.first_isPolyTime
  have hm := TM2ContextMapGeneric.contextMap_isPolyTime each he
  have hmap : ComplexityTheory.IsPolyTime mapped := TM2Compose.isPolyTime_comp swap (TM2ContextMapGeneric.contextMap each) hs hm
  have h := TM2Compose.isPolyTime_comp mapped (List.flatten : List (List Bool) → List Bool) hmap TM2FlattenList.flatten_isPolyTime
  have heq : (fun p => (mapped p).flatten) = productBits := by
    funext p
    rfl
  rw [heq] at h
  exact h

def product (p : List Bool × List Bool) : Nat := (productBits p).length

theorem product_correct (a b : List Bool) : product (a,b) = a.length*b.length := productBits_length a b

theorem product_isPolyTime : ComplexityTheory.IsPolyTime product :=
  TM2Compose.isPolyTime_comp productBits List.length productBits_isPolyTime TM2BinaryListLength.length_isPolyTime

namespace Fixtures
example : product ([],[true]) = 0 := rfl
example : product ([true,false],[false,true,true]) = 6 := rfl
end Fixtures
end Shared.ComplexityBridge.TM2UnaryProductLength
