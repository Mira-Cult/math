import Shared.ComplexityBridge.TM2ContextMapIO
import Shared.ComplexityBridge.TM2PairFirst
import Shared.ComplexityBridge.CNFBinaryIncrement
import Shared.ComplexityBridge.TM2FlattenList

set_option backward.isDefEq.respectTransparency false

/-! Polynomial-time loop bodies for the indexed `guardAll` traversal. These
are finite TM2 computations on the actual canonical encodings; the repeated
outer-list driver is not supplied here. -/
namespace Shared.ComplexityBridge.TM2GuardAllStep
open Shared.ComplexityBridge.CNF Shared.ComplexityBridge.CNFDisjunction

/-- Two polynomial-time functions can return their results as one pair. The
input copy, both computations and pair serialization are explicitly charged. -/
theorem pair_isPolyTime {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
    (F : α → β) (G : α → γ) (hF : ComplexityTheory.IsPolyTime F) (hG : ComplexityTheory.IsPolyTime G) :
    ComplexityTheory.IsPolyTime (fun x => (F x,G x)) := by
  let keep : α → β × α := fun x => (F x,x)
  let second : β × α → β × γ := fun p => (p.1,G p.2)
  have hk : ComplexityTheory.IsPolyTime keep := Shared.ComplexityBridge.TM2GenericDiagonal.withInput_isPolyTime F hF
  have hs : ComplexityTheory.IsPolyTime second := Shared.ComplexityBridge.TM2PairSwap.mapSecond_isPolyTime G hG
  exact Shared.ComplexityBridge.TM2Compose.isPolyTime_comp keep second hk hs

theorem second_isPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β] :
    ComplexityTheory.IsPolyTime (fun p : α × β => p.2) := by
  let swap : α × β → β × α := Shared.ComplexityBridge.TM2PairSwap.swap
  have hs : ComplexityTheory.IsPolyTime swap := Shared.ComplexityBridge.TM2PairSwap.swap_isPolyTime
  have hf : ComplexityTheory.IsPolyTime (Shared.ComplexityBridge.TM2PairFirst.first (α := β) (β := α)) :=
    Shared.ComplexityBridge.TM2PairFirst.first_isPolyTime
  have hc := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp swap
    (Shared.ComplexityBridge.TM2PairFirst.first (α := β) (β := α)) hs hf
  simpa [swap,Shared.ComplexityBridge.TM2PairFirst.first,Shared.ComplexityBridge.TM2PairSwap.swap] using hc

def guardedAppend (p : (Nat × Formula) × Formula) : Formula :=
  p.2 ++ guardFormula p.1.1 p.1.2

theorem guardedAppend_isPolyTime : ComplexityTheory.IsPolyTime guardedAppend := by
  let G : Nat × Formula → Formula := fun z => guardFormula z.1 z.2
  let map : (Nat × Formula) × Formula → Formula × Formula :=
    Shared.ComplexityBridge.TM2TypedPairMap.pairMap G
  let swap : Formula × Formula → Formula × Formula := Shared.ComplexityBridge.TM2PairSwap.swap
  let app : Formula × Formula → Formula := Shared.ComplexityBridge.TM2ListAppend.append
  have hg : ComplexityTheory.IsPolyTime G := Shared.ComplexityBridge.TM2ContextMapIO.guardFormula_isPolyTime
  have hm : ComplexityTheory.IsPolyTime map := Shared.ComplexityBridge.TM2TypedPairMap.pairMap_isPolyTime G hg
  have hs : ComplexityTheory.IsPolyTime swap := Shared.ComplexityBridge.TM2PairSwap.swap_isPolyTime
  have ha : ComplexityTheory.IsPolyTime app := Shared.ComplexityBridge.TM2ListAppend.append_isPolyTime
  have h₁ := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp map swap hm hs
  have h₂ := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp (fun x => swap (map x)) app h₁ ha
  change ComplexityTheory.IsPolyTime (fun p : (Nat × Formula) × Formula => p.2 ++ guardFormula p.1.1 p.1.2)
  simpa [G,map,swap,app,Shared.ComplexityBridge.TM2TypedPairMap.pairMap,
    Shared.ComplexityBridge.TM2PairSwap.swap,Shared.ComplexityBridge.TM2ListAppend.append] using h₂

def stateStep (p : (Nat × Formula) × Formula) : Nat × Formula :=
  (p.1.1+1, p.1.2 ++ guardFormula p.1.1 p.2)

/-- The exact fold step advances the index and appends the guarded next
formula to the existing accumulator, with a fixed polynomial-time machine. -/
theorem stateStep_isPolyTime : ComplexityTheory.IsPolyTime stateStep := by
  let fstState : (Nat × Formula) × Formula → Nat × Formula := Shared.ComplexityBridge.TM2PairFirst.first
  let firstIndex : Nat × Formula → Nat := Shared.ComplexityBridge.TM2PairFirst.first
  let firstAcc : Nat × Formula → Formula := fun p => p.2
  let nextFormula : (Nat × Formula) × Formula → Formula := fun p => p.2
  have hstate : ComplexityTheory.IsPolyTime fstState := Shared.ComplexityBridge.TM2PairFirst.first_isPolyTime
  have hidx : ComplexityTheory.IsPolyTime firstIndex := Shared.ComplexityBridge.TM2PairFirst.first_isPolyTime
  have hacc : ComplexityTheory.IsPolyTime firstAcc := second_isPolyTime
  have hform : ComplexityTheory.IsPolyTime nextFormula := second_isPolyTime
  let index : (Nat × Formula) × Formula → Nat := fun p => firstIndex (fstState p)
  let acc : (Nat × Formula) × Formula → Formula := fun p => firstAcc (fstState p)
  have hi : ComplexityTheory.IsPolyTime index := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp fstState firstIndex hstate hidx
  have ha : ComplexityTheory.IsPolyTime acc := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp fstState firstAcc hstate hacc
  let request : (Nat × Formula) × Formula → (Nat × Formula) × Formula := fun p => ((index p,nextFormula p),acc p)
  have hr : ComplexityTheory.IsPolyTime request := pair_isPolyTime _ _ (pair_isPolyTime _ _ hi hform) ha
  let next : (Nat × Formula) × Formula → Nat := fun p => Nat.succ (index p)
  have hn : ComplexityTheory.IsPolyTime next := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp index Nat.succ hi
    Shared.ComplexityBridge.CNFBinaryIncrement.successor_isPolyTime
  let joined : (Nat × Formula) × Formula → Formula := fun p => guardedAppend (request p)
  have hj : ComplexityTheory.IsPolyTime joined := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp request guardedAppend hr guardedAppend_isPolyTime
  have h := pair_isPolyTime next joined hn hj
  change ComplexityTheory.IsPolyTime (fun p : (Nat × Formula) × Formula =>
    (p.1.1+1,p.1.2 ++ guardFormula p.1.1 p.2))
  simpa [next,joined,request,index,acc,firstIndex,firstAcc,fstState,nextFormula,
    guardedAppend,Shared.ComplexityBridge.TM2PairFirst.first] using h

def foldStep (state : Nat × Formula) (f : Formula) : Nat × Formula := stateStep (state,f)

theorem foldStep_correct (i : Nat) (acc : Formula) (fs : List Formula) :
    fs.foldl foldStep (i,acc) = (i+fs.length,acc++guardAll i fs) := by
  induction fs generalizing i acc with
  | nil => simp [guardAll]
  | cons f fs ih =>
    simp only [List.foldl_cons,foldStep,stateStep,ih,guardAll,List.length_cons]
    congr 1
    · omega
    · simp [List.append_assoc]


/-- Repeated binary successor grows its encoded length by at most one per
increment, independent of the numerical magnitude of the starting index. -/
theorem index_bits_add (i k : Nat) :
    (BitstringEncoding.bitEncode (i+k)).length ≤ (BitstringEncoding.bitEncode i).length+k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := Shared.Codes.BitTableValidation.increment_length (i+k).bits
    rw [Shared.ComplexityBridge.CNFBinaryIncrement.increment_bits] at h
    change (Computability.encodeNat (i+k)).length ≤ (Computability.encodeNat i).length+k at ih
    change (Computability.encodeNat (i+(k+1))).length ≤ (Computability.encodeNat i).length+(k+1)
    simp only [Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits] at ih ⊢
    have he : i+(k+1) = (i+k)+1 := by omega
    rw [he]
    omega

/-- The serialized result of any processed prefix is uniformly polynomial in
the full original `(start, formulas)` request. This is a size bound, not an
outer-loop running-time theorem. -/
theorem guardAll_prefix_size :
    ∃ q : Polynomial Nat, ∀ (i : Nat) (fs : List Formula) (k : Nat),
      (BitstringEncoding.bitEncode (guardAll i (fs.take k))).length ≤
        q.eval (BitstringEncoding.bitEncode (i,fs)).length := by
  obtain ⟨r,hr⟩ := Shared.ComplexityBridge.TM2MapSizeBounds.output_length_poly
    (fun z : Nat × Formula => guardFormula z.1 z.2)
    Shared.ComplexityBridge.TM2ContextMapIO.guardFormula_isPolyTime
  let q : Polynomial Nat := Polynomial.X * r.comp (Polynomial.C 5*Polynomial.X+Polynomial.C 1)
  refine ⟨q,?_⟩
  intro i fs k
  let N := (BitstringEncoding.bitEncode (i,fs)).length
  have hcount : fs.length ≤ N := by
    have h := Shared.ComplexityBridge.CNF.list_length_le_bitEncode fs
    change fs.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode fs).length
    simp only [List.length_append]
    omega
  have hi : (BitstringEncoding.bitEncode i).length ≤ N := by
    change (BitstringEncoding.bitEncode i).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode fs).length
    simp only [List.length_append,BitstringEncoding.length_delimit]
    omega
  have hformula : ∀ f ∈ fs, (BitstringEncoding.bitEncode f).length ≤ N := by
    intro f hf
    have h := Shared.ComplexityBridge.TM2MapSizeBounds.element_length_le hf
    change (BitstringEncoding.bitEncode f).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode fs).length
    simp only [List.length_append]
    omega
  have hloop : ∀ (xs : List Formula) (j : Nat), (∀ f ∈ xs, f ∈ fs) → j+xs.length ≤ fs.length →
      (BitstringEncoding.bitEncode (guardAll (i+j) xs)).length ≤ xs.length*r.eval (5*N+1) := by
    intro xs
    induction xs with
    | nil =>
      intro j _ _
      have he : BitstringEncoding.bitEncode ([] : Formula) = [] := rfl
      simp [guardAll,he]
    | cons f xs ih =>
      intro j hsub hlen
      have hf : f ∈ fs := hsub f (by simp)
      have hsub' : ∀ x ∈ xs, x ∈ fs := by intro x hx; exact hsub x (by simp [hx])
      have hlen' : (j+1)+xs.length ≤ fs.length := by simp only [List.length_cons] at hlen; omega
      have hb := index_bits_add i j
      have hpair : (BitstringEncoding.bitEncode (i+j,f)).length ≤ 5*N+1 := by
        change (BitstringEncoding.delimit (BitstringEncoding.bitEncode (i+j))++BitstringEncoding.bitEncode f).length ≤ _
        simp only [List.length_append,BitstringEncoding.length_delimit]
        have hfsize := hformula f hf
        omega
      have hout := le_trans (hr (i+j,f)) (Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono r hpair)
      change (BitstringEncoding.bitEncode (guardFormula (i+j) f)).length ≤ r.eval (5*N+1) at hout
      have htail := ih (j+1) hsub' hlen'
      have he : (i+j)+1 = i+(j+1) := by omega
      rw [guardAll,Shared.ComplexityBridge.TM2ListAppend.list_encoding_append,List.length_append,he]
      rw [List.length_cons,Nat.succ_mul]
      omega
  have hpref : ∀ f ∈ fs.take k, f ∈ fs := by
    intro f hf; exact (List.take_sublist k fs).subset hf
  have htake : (fs.take k).length ≤ fs.length := (List.take_sublist k fs).length_le
  have hb := hloop (fs.take k) 0 hpref (by omega)
  simp only [Nat.add_zero] at hb
  have hm := Nat.mul_le_mul_right (r.eval (5*N+1)) (le_trans htake hcount)
  change (BitstringEncoding.bitEncode (guardAll i (fs.take k))).length ≤ q.eval N
  simp only [q,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_add,
    Polynomial.eval_C]
  omega


/-- One fixed concrete outer-step machine runs within a polynomial in the
whole original request at every valid prefix. The encoded intermediate
accumulator and incremented binary index are included in that clock. -/
theorem stateStep_prefix_run :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial Nat,
      ∀ (i : Nat) (fs : List Formula) (k : Nat) (f : Formula),
        k ≤ fs.length → f ∈ fs →
      ∃ t ≤ p.eval (BitstringEncoding.bitEncode (i,fs)).length,
        Shared.ComplexityBridge.TM2Symbols.runSteps core.tm.step t
          (Turing.initList core.tm ((BitstringEncoding.bitEncode
            ((i+k,guardAll i (fs.take k)),f)).map core.inputAlphabet.symm)) =
        some (Turing.haltList core.tm ((BitstringEncoding.bitEncode
          (stateStep ((i+k,guardAll i (fs.take k)),f))).map core.outputAlphabet.symm)) := by
  obtain ⟨q,hq⟩ := guardAll_prefix_size
  obtain ⟨core⟩ := stateStep_isPolyTime
  let p : Polynomial Nat := core.time.comp (Polynomial.C 9*Polynomial.X+Polynomial.C 2*q+Polynomial.C 3)
  refine ⟨core.toTM2ComputableAux,p,?_⟩
  intro i fs k f hk hf
  let N := (BitstringEncoding.bitEncode (i,fs)).length
  let request := ((i+k,guardAll i (fs.take k)),f)
  have hcount : fs.length ≤ N := by
    have hh := Shared.ComplexityBridge.CNF.list_length_le_bitEncode fs
    change fs.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode fs).length
    simp only [List.length_append]
    omega
  have hi : (BitstringEncoding.bitEncode i).length ≤ N := by
    change (BitstringEncoding.bitEncode i).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode fs).length
    simp only [List.length_append,BitstringEncoding.length_delimit]
    omega
  have hfsize : (BitstringEncoding.bitEncode f).length ≤ N := by
    have hh := Shared.ComplexityBridge.TM2MapSizeBounds.element_length_le hf
    change (BitstringEncoding.bitEncode f).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode fs).length
    simp only [List.length_append]
    omega
  have hacc := hq i fs k
  have hidx := index_bits_add i k
  have hsize : (BitstringEncoding.bitEncode request).length ≤ 9*N+2*q.eval N+3 := by
    change (BitstringEncoding.delimit
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode (i+k))++BitstringEncoding.bitEncode (guardAll i (fs.take k)))++
      BitstringEncoding.bitEncode f).length ≤ _
    simp only [List.length_append,BitstringEncoding.length_delimit]
    dsimp [N] at *
    omega
  let run := core.outputsFun request
  refine ⟨run.steps,?_,?_⟩
  · have hm := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono core.time hsize
    have ht := le_trans run.steps_le_m hm
    change run.steps ≤ p.eval N
    simp only [p,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    exact ht
  · rw [Shared.ComplexityBridge.TM2Symbols.runSteps_iterate]
    exact run.evals_in_steps

namespace Fixtures
example : foldStep (0,[]) [] = (1,[]) := rfl
example : guardAll 0 [[],[]] = [] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2GuardAllStep
