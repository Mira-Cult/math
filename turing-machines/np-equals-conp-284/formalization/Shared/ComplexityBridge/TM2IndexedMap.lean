import Shared.ComplexityBridge.TM2GateFold

set_option backward.isDefEq.respectTransparency false

/-! A generic indexed traversal. The clock and all intermediate sizes are
measured in the complete canonical encoding of the initial index and list. -/
namespace Shared.ComplexityBridge.TM2IndexedMap
open Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2Program

variable {α β : Type} [BitstringEncoding α] [BitstringEncoding β]

def indexed (F : Nat × α → β) : Nat → List α → List β
  | _, [] => []
  | i, x::xs => F (i,x) :: indexed F (i+1) xs

def step (F : Nat × α → β) (p : (Nat × List β) × α) : Nat × List β :=
  (p.1.1+1,p.1.2 ++ [F (p.1.1,p.2)])

theorem step_isPolyTime (F : Nat × α → β) (hF : ComplexityTheory.IsPolyTime F) :
    ComplexityTheory.IsPolyTime (step F) := by
  let state : (Nat × List β) × α → Nat × List β := fun p => p.1
  let item : (Nat × List β) × α → α := fun p => p.2
  let idx : (Nat × List β) × α → Nat := fun p => p.1.1
  let acc : (Nat × List β) × α → List β := fun p => p.1.2
  let args : (Nat × List β) × α → Nat × α := fun p => (idx p,item p)
  let next : (Nat × List β) × α → Nat := fun p => Nat.succ (idx p)
  let val : (Nat × List β) × α → β := fun p => F (args p)
  let single : (Nat × List β) × α → List β := fun p => [val p]
  let joined : (Nat × List β) × α → List β := fun p => acc p ++ single p
  have hs : ComplexityTheory.IsPolyTime state := TM2PairFirst.first_isPolyTime
  have hg : ComplexityTheory.IsPolyTime item := TM2GuardAllStep.second_isPolyTime
  have hi : ComplexityTheory.IsPolyTime idx := TM2Compose.isPolyTime_comp state (fun p : Nat × List β => p.1) hs TM2PairFirst.first_isPolyTime
  have ha : ComplexityTheory.IsPolyTime acc := TM2Compose.isPolyTime_comp state (fun p : Nat × List β => p.2) hs TM2GuardAllStep.second_isPolyTime
  have hr : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime idx item hi hg
  have hn : ComplexityTheory.IsPolyTime next := TM2Compose.isPolyTime_comp idx Nat.succ hi CNFBinaryIncrement.successor_isPolyTime
  have hv : ComplexityTheory.IsPolyTime val := TM2Compose.isPolyTime_comp args F hr hF
  have hc : ComplexityTheory.IsPolyTime single := TM2GateCNFPieces.singleton_isPolyTime val hv
  have hp := TM2GuardAllStep.pair_isPolyTime acc single ha hc
  have hj : ComplexityTheory.IsPolyTime joined := TM2Compose.isPolyTime_comp (fun p => (acc p,single p)) TM2ListAppend.append hp TM2ListAppend.append_isPolyTime
  have h := TM2GuardAllStep.pair_isPolyTime next joined hn hj
  change ComplexityTheory.IsPolyTime (fun p : (Nat × List β) × α => (p.1.1+1,p.1.2++[F (p.1.1,p.2)]))
  simpa [next,joined,single,val,args,acc,idx,item,Nat.succ_eq_add_one] using h

omit [BitstringEncoding α] [BitstringEncoding β] in
theorem fold_correct (F : Nat × α → β) (i : Nat) (acc : List β) (xs : List α) :
    TM2PolynomialFold.fold (step F) (i,acc) xs = (i+xs.length,acc++indexed F i xs) := by
  induction xs generalizing i acc with
  | nil => simp [TM2PolynomialFold.fold,indexed]
  | cons x xs ih =>
    change TM2PolynomialFold.fold (step F) (step F ((i,acc),x)) xs = _
    rw [show step F ((i,acc),x) = (i+1,acc++[F (i,x)]) by rfl,ih]
    simp [indexed,List.append_assoc,Nat.add_comm,Nat.add_left_comm]

theorem prefix_size (F : Nat × α → β) (hF : ComplexityTheory.IsPolyTime F) :
    ∃ q : Polynomial Nat, ∀ (i : Nat) (xs : List α) (k : Nat),
      (BitstringEncoding.bitEncode (indexed F i (xs.take k))).length ≤
        q.eval (BitstringEncoding.bitEncode (i,xs)).length := by
  obtain ⟨r,hr⟩ := TM2MapSizeBounds.output_length_poly F hF
  let q : Polynomial Nat := Polynomial.X * (Polynomial.C 2 * r.comp (Polynomial.C 5*Polynomial.X+Polynomial.C 1) + Polynomial.C 1)
  refine ⟨q,?_⟩
  intro i xs k
  let N := (BitstringEncoding.bitEncode (i,xs)).length
  have hcount : xs.length ≤ N := by
    have h := CNF.list_length_le_bitEncode xs
    change xs.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode xs).length
    simp only [List.length_append]; omega
  have hi : (BitstringEncoding.bitEncode i).length ≤ N := by
    change (BitstringEncoding.bitEncode i).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode xs).length
    simp only [List.length_append,BitstringEncoding.length_delimit]; omega
  have hitem : ∀ x ∈ xs, (BitstringEncoding.bitEncode x).length ≤ N := by
    intro x hx
    have h := TM2MapSizeBounds.element_length_le hx
    change (BitstringEncoding.bitEncode x).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode xs).length
    simp only [List.length_append]; omega
  have hloop : ∀ (ys : List α) (j : Nat), (∀ x ∈ ys, x ∈ xs) → j+ys.length ≤ xs.length →
      (BitstringEncoding.bitEncode (indexed F (i+j) ys)).length ≤ ys.length*(2*r.eval (5*N+1)+1) := by
    intro ys
    induction ys with
    | nil =>
      intro j _ _
      have he : BitstringEncoding.bitEncode ([] : List β) = [] := rfl
      simp [indexed,he]
    | cons x ys ih =>
      intro j hsub hlen
      have hx : x ∈ xs := hsub x (by simp)
      have hsub' : ∀ y ∈ ys, y ∈ xs := by intro y hy; exact hsub y (by simp [hy])
      have hlen' : (j+1)+ys.length ≤ xs.length := by simp only [List.length_cons] at hlen; omega
      have hb := TM2GuardAllStep.index_bits_add i j
      have hpair : (BitstringEncoding.bitEncode (i+j,x)).length ≤ 5*N+1 := by
        change (BitstringEncoding.delimit (BitstringEncoding.bitEncode (i+j))++BitstringEncoding.bitEncode x).length ≤ _
        simp only [List.length_append,BitstringEncoding.length_delimit]
        have hxsize := hitem x hx
        omega
      have hout := le_trans (hr (i+j,x)) (TM2Compose.polynomial_eval_mono r hpair)
      have htail := ih (j+1) hsub' hlen'
      have he : (i+j)+1 = i+(j+1) := by omega
      rw [indexed,TM2MapSizeBounds.encode_cons,List.length_append,BitstringEncoding.length_delimit,he,List.length_cons]
      have hm : (ys.length+1)*(2*r.eval (5*N+1)+1) = ys.length*(2*r.eval (5*N+1)+1)+(2*r.eval (5*N+1)+1) := by ring
      rw [hm]
      omega
  have hpref : ∀ x ∈ xs.take k, x ∈ xs := by intro x hx; exact (List.take_sublist k xs).subset hx
  have htake : (xs.take k).length ≤ xs.length := (List.take_sublist k xs).length_le
  have hb := hloop (xs.take k) 0 hpref (by omega)
  simp only [Nat.add_zero] at hb
  have hm := Nat.mul_le_mul_right (2*r.eval (5*N+1)+1) (le_trans htake hcount)
  change (BitstringEncoding.bitEncode (indexed F i (xs.take k))).length ≤ q.eval N
  simp only [q,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_C]
  omega

namespace Fixtures
example : indexed (fun p : Nat × Nat => p.1+p.2) 5 [2,3] = [7,9] := rfl
example : indexed (fun p : Nat × Nat => p.1+p.2) 5 [] = [] := rfl
end Fixtures

end Shared.ComplexityBridge.TM2IndexedMap
