import Shared.ComplexityBridge.TM2GateDispatch
import Shared.ComplexityBridge.TM2PolynomialFold
import Shared.ComplexityBridge.TM2FoldIO

/-! Indexed gate-list fold using the actual per-gate finite machine. The
prefix bounds include gate encodings and the growing binary wire index. -/
namespace Shared.ComplexityBridge.TM2GateFold
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2Program

def step (p : (Nat × Formula) × Gate) : Nat × Formula :=
  (p.1.1+1,p.1.2 ++ gateCNF p.1.1 p.2)

theorem step_isPolyTime : ComplexityTheory.IsPolyTime step := by
  let state : (Nat × Formula) × Gate → Nat × Formula := fun p => p.1
  let gate : (Nat × Formula) × Gate → Gate := fun p => p.2
  let idx : (Nat × Formula) × Gate → Nat := fun p => p.1.1
  let acc : (Nat × Formula) × Gate → Formula := fun p => p.1.2
  let args : (Nat × Formula) × Gate → Nat × Gate := fun p => (idx p,gate p)
  let next : (Nat × Formula) × Gate → Nat := fun p => Nat.succ (idx p)
  let clauses : (Nat × Formula) × Gate → Formula := fun p => gateCNF (idx p) (gate p)
  let joined : (Nat × Formula) × Gate → Formula := fun p => acc p ++ clauses p
  have hs : ComplexityTheory.IsPolyTime state := TM2PairFirst.first_isPolyTime
  have hg : ComplexityTheory.IsPolyTime gate := TM2GuardAllStep.second_isPolyTime
  have hi : ComplexityTheory.IsPolyTime idx := TM2Compose.isPolyTime_comp state (fun p : Nat × Formula => p.1) hs TM2PairFirst.first_isPolyTime
  have ha : ComplexityTheory.IsPolyTime acc := TM2Compose.isPolyTime_comp state (fun p : Nat × Formula => p.2) hs TM2GuardAllStep.second_isPolyTime
  have hr : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime idx gate hi hg
  have hn : ComplexityTheory.IsPolyTime next := TM2Compose.isPolyTime_comp idx Nat.succ hi CNFBinaryIncrement.successor_isPolyTime
  have hf : ComplexityTheory.IsPolyTime clauses := TM2Compose.isPolyTime_comp args (fun p : Nat × Gate => gateCNF p.1 p.2) hr TM2GateDispatch.gateCNF_isPolyTime
  have hj : ComplexityTheory.IsPolyTime joined := TM2GateDispatch.append_isPolyTime acc clauses ha hf
  have h := TM2GuardAllStep.pair_isPolyTime next joined hn hj
  change ComplexityTheory.IsPolyTime (fun p : (Nat × Formula) × Gate => (p.1.1+1,p.1.2++gateCNF p.1.1 p.2))
  simpa [next,joined,acc,clauses,idx,gate,Nat.succ_eq_add_one] using h

theorem gateConstraints_append (i : Nat) (xs ys : List Gate) :
    gateConstraints i (xs++ys) = gateConstraints i xs ++ gateConstraints (i+xs.length) ys := by
  induction xs generalizing i with
  | nil => simp [gateConstraints]
  | cons g xs ih =>
    simp [gateConstraints,ih,List.append_assoc,Nat.add_comm,Nat.add_left_comm]

theorem fold_correct (i : Nat) (acc : Formula) (gs : List Gate) :
    TM2PolynomialFold.fold step (i,acc) gs = (i+gs.length,acc++gateConstraints i gs) := by
  induction gs generalizing i acc with
  | nil => simp [TM2PolynomialFold.fold,gateConstraints]
  | cons g gs ih =>
    change TM2PolynomialFold.fold step (step ((i,acc),g)) gs = _
    rw [show step ((i,acc),g) = (i+1,acc++gateCNF i g) by rfl,ih]
    simp [gateConstraints,List.append_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Serialized output of every gate-list prefix is uniformly polynomial in
its entire input, even for arbitrary binary initial wire indices. -/
theorem prefix_size :
    ∃ q : Polynomial Nat, ∀ (i : Nat) (gs : List Gate) (k : Nat),
      (BitstringEncoding.bitEncode (gateConstraints i (gs.take k))).length ≤
        q.eval (BitstringEncoding.bitEncode (i,gs)).length := by
  obtain ⟨r,hr⟩ := TM2MapSizeBounds.output_length_poly
    (fun z : Nat × Gate => gateCNF z.1 z.2) TM2GateDispatch.gateCNF_isPolyTime
  let q : Polynomial Nat := Polynomial.X * r.comp (Polynomial.C 5*Polynomial.X+Polynomial.C 1)
  refine ⟨q,?_⟩
  intro i gs k
  let N := (BitstringEncoding.bitEncode (i,gs)).length
  have hcount : gs.length ≤ N := by
    have h := CNF.list_length_le_bitEncode gs
    change gs.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode gs).length
    simp only [List.length_append]
    omega
  have hi : (BitstringEncoding.bitEncode i).length ≤ N := by
    change (BitstringEncoding.bitEncode i).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode gs).length
    simp only [List.length_append,BitstringEncoding.length_delimit]
    omega
  have hgate : ∀ g ∈ gs, (BitstringEncoding.bitEncode g).length ≤ N := by
    intro g hg
    have h := TM2MapSizeBounds.element_length_le hg
    change (BitstringEncoding.bitEncode g).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode gs).length
    simp only [List.length_append]
    omega
  have hloop : ∀ (xs : List Gate) (j : Nat), (∀ g ∈ xs, g ∈ gs) → j+xs.length ≤ gs.length →
      (BitstringEncoding.bitEncode (gateConstraints (i+j) xs)).length ≤ xs.length*r.eval (5*N+1) := by
    intro xs
    induction xs with
    | nil =>
      intro j _ _
      have he : BitstringEncoding.bitEncode ([] : Formula) = [] := rfl
      simp [gateConstraints,he]
    | cons g xs ih =>
      intro j hsub hlen
      have hg : g ∈ gs := hsub g (by simp)
      have hsub' : ∀ x ∈ xs, x ∈ gs := by intro x hx; exact hsub x (by simp [hx])
      have hlen' : (j+1)+xs.length ≤ gs.length := by simp only [List.length_cons] at hlen; omega
      have hb := TM2GuardAllStep.index_bits_add i j
      have hpair : (BitstringEncoding.bitEncode (i+j,g)).length ≤ 5*N+1 := by
        change (BitstringEncoding.delimit (BitstringEncoding.bitEncode (i+j))++BitstringEncoding.bitEncode g).length ≤ _
        simp only [List.length_append,BitstringEncoding.length_delimit]
        have hgsize := hgate g hg
        omega
      have hout := le_trans (hr (i+j,g)) (TM2Compose.polynomial_eval_mono r hpair)
      change (BitstringEncoding.bitEncode (gateCNF (i+j) g)).length ≤ r.eval (5*N+1) at hout
      have htail := ih (j+1) hsub' hlen'
      have he : (i+j)+1 = i+(j+1) := by omega
      rw [gateConstraints,TM2ListAppend.list_encoding_append,List.length_append,he]
      rw [List.length_cons,Nat.succ_mul]
      omega
  have hpref : ∀ g ∈ gs.take k, g ∈ gs := by intro g hg; exact (List.take_sublist k gs).subset hg
  have htake : (gs.take k).length ≤ gs.length := (List.take_sublist k gs).length_le
  have hb := hloop (gs.take k) 0 hpref (by omega)
  simp only [Nat.add_zero] at hb
  have hm := Nat.mul_le_mul_right (r.eval (5*N+1)) (le_trans htake hcount)
  change (BitstringEncoding.bitEncode (gateConstraints i (gs.take k))).length ≤ q.eval N
  simp only [q,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_C]
  omega

end Shared.ComplexityBridge.TM2GateFold
