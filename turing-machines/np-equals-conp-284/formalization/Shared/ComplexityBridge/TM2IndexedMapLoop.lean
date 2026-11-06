import Shared.ComplexityBridge.TM2IndexedMap

set_option backward.isDefEq.respectTransparency false

/-! Whole indexed map fold with a uniform clock, including every call to the
actual supplied element machine. Input/output boundary work is separate. -/
namespace Shared.ComplexityBridge.TM2IndexedMapLoop
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2Program

variable {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
variable (F : Nat × α → β) (hF : ComplexityTheory.IsPolyTime F)
open Shared.ComplexityBridge.TM2IndexedMap

include hF

/-- Each prefix evaluator terminates within one polynomial in the original
request. The same polynomial bounds every intermediate serialized value. -/
theorem bounded_step :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ B : Polynomial Nat,
      ∀ (i : Nat) (gs pref : List α) (g : α) (tail : List α), gs = pref++g::tail →
        let state := TM2PolynomialFold.fold (step F) (i,([] : List β)) pref
        let size := B.eval (BitstringEncoding.bitEncode (i,gs)).length
        ∃ n ≤ size,
          runSteps core.tm.step n
            (Turing.initList core.tm ((BitstringEncoding.bitEncode (state,g)).map core.inputAlphabet.symm)) =
            some (Turing.haltList core.tm ((BitstringEncoding.bitEncode (step F (state,g))).map core.outputAlphabet.symm)) ∧
          (BitstringEncoding.bitEncode state).length ≤ size ∧
          (BitstringEncoding.bitEncode g).length ≤ size ∧
          (BitstringEncoding.bitEncode (state,g)).length ≤ size ∧
          (BitstringEncoding.bitEncode (step F (state,g))).length ≤ size := by
  obtain ⟨q,hq⟩ := prefix_size F hF
  obtain ⟨r,hr⟩ := TM2MapSizeBounds.output_length_poly (step F) (step_isPolyTime F hF)
  obtain ⟨core⟩ := step_isPolyTime F hF
  let Q : Polynomial Nat := Polynomial.C 9*Polynomial.X+Polynomial.C 2*q+Polynomial.C 3
  let B : Polynomial Nat := Q+core.time.comp Q+r.comp Q
  refine ⟨core.toTM2ComputableAux,B,?_⟩
  intro i gs pref g tail hsplit
  let N := (BitstringEncoding.bitEncode (i,gs)).length
  have hk : pref.length ≤ gs.length := by rw [hsplit,List.length_append]; simp
  have hg : g ∈ gs := by rw [hsplit]; simp
  have htake : gs.take pref.length = pref := by rw [hsplit]; simp
  have hcount : gs.length ≤ N := by
    have hh := CNF.list_length_le_bitEncode gs
    change gs.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode gs).length
    simp only [List.length_append]; omega
  have hi : (BitstringEncoding.bitEncode i).length ≤ N := by
    change (BitstringEncoding.bitEncode i).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode gs).length
    simp only [List.length_append,BitstringEncoding.length_delimit]; omega
  have hgsize : (BitstringEncoding.bitEncode g).length ≤ N := by
    have hh := TM2MapSizeBounds.element_length_le hg
    change (BitstringEncoding.bitEncode g).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode gs).length
    simp only [List.length_append]; omega
  have hacc := hq i gs pref.length
  rw [htake] at hacc
  have hidx := TM2GuardAllStep.index_bits_add i pref.length
  let state := (i+pref.length,indexed F i pref)
  have hf : TM2PolynomialFold.fold (step F) (i,([] : List β)) pref = state := by
    simpa [state] using fold_correct F i [] pref
  have hstate : (BitstringEncoding.bitEncode state).length ≤ 4*N+q.eval N+1 := by
    change (BitstringEncoding.delimit (BitstringEncoding.bitEncode (i+pref.length))++
      BitstringEncoding.bitEncode (indexed F i pref)).length ≤ _
    simp only [List.length_append,BitstringEncoding.length_delimit]
    dsimp [N] at *; omega
  have hpair : (BitstringEncoding.bitEncode (state,g)).length ≤ Q.eval N := by
    change (BitstringEncoding.delimit (BitstringEncoding.bitEncode state)++BitstringEncoding.bitEncode g).length ≤ Q.eval N
    simp only [List.length_append,BitstringEncoding.length_delimit,Q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega
  have hout : (BitstringEncoding.bitEncode (step F (state,g))).length ≤ r.eval (Q.eval N) :=
    le_trans (hr (state,g)) (TM2Compose.polynomial_eval_mono r hpair)
  let run := core.outputsFun (state,g)
  have htime : run.steps ≤ core.time.eval (Q.eval N) :=
    le_trans run.steps_le_m (TM2Compose.polynomial_eval_mono core.time hpair)
  have hB : B.eval N = Q.eval N+core.time.eval (Q.eval N)+r.eval (Q.eval N) := by
    simp [B,Polynomial.eval_add,Polynomial.eval_comp]
  change ∃ n ≤ B.eval N, runSteps core.tm.step n
    (Turing.initList core.tm ((BitstringEncoding.bitEncode (TM2PolynomialFold.fold (step F) (i,[]) pref,g)).map core.inputAlphabet.symm)) =
    some (Turing.haltList core.tm ((BitstringEncoding.bitEncode (step F (TM2PolynomialFold.fold (step F) (i,[]) pref,g))).map core.outputAlphabet.symm)) ∧ _
  rw [hf]
  refine ⟨run.steps,?_,?_,?_,?_,?_,?_⟩
  · rw [hB]; omega
  · rw [runSteps_iterate]; exact run.evals_in_steps
  · rw [hB]; simp [Q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X] at hpair ⊢; omega
  · rw [hB]; simp [Q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X] at hpair ⊢; omega
  · rw [hB]; omega
  · rw [hB]; omega

/-- Starting with an empty list accumulator, the complete finite indexed traversal
reaches the done state after a polynomial number of target blocks. -/
theorem loop_done :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ P : Polynomial Nat,
      ∀ (i : Nat) (gs : List α), ∃ t ≤ P.eval (BitstringEncoding.bitEncode (i,gs)).length,
        runSteps (TM2FoldHandoff.machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
            (TM2ContextMapCall.srcEmbed core.tm
              (TM2ContextMapSplit.cfg (.inr .header) none
                (BitstringEncoding.bitEncode (i,([] : List β))) [] [] [] [] (BitstringEncoding.bitEncode gs))
              (Turing.initList core.tm []).stk)) =
        some (TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
          (TM2ContextMapCall.srcEmbed core.tm
            (TM2ContextMapSplit.cfg (.inr .done) none
              (BitstringEncoding.bitEncode (i+gs.length,indexed F i gs)) [] [] [] [] [])
            (Turing.initList core.tm []).stk)) := by
  obtain ⟨core,B,hB⟩ := bounded_step F hF
  let P : Polynomial Nat := Polynomial.X*(Polynomial.C 16*B+Polynomial.C 16)+Polynomial.C 1
  refine ⟨core,P,?_⟩
  intro i gs
  let N := (BitstringEncoding.bitEncode (i,gs)).length
  obtain ⟨t,ht,hr⟩ := TM2PolynomialFold.loop_done (step F) core (i,([] : List β)) gs (B.eval N) (hB i gs)
  have hc : gs.length ≤ N := by
    have hh := CNF.list_length_le_bitEncode gs
    change gs.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode gs).length
    simp only [List.length_append]; omega
  have hm := Nat.mul_le_mul_right (16*B.eval N+16) hc
  refine ⟨t,?_,?_⟩
  · change t ≤ P.eval N
    simp only [P,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega
  · simpa [fold_correct F] using hr

open TM2FoldIO

def foldResult (F : Nat × α → β) (p : Nat × List α) : Nat × List β :=
  (p.1+p.2.length,indexed F p.1 p.2)

/-- Complete finite TM2 run on the canonical request, with the final fold
state in the standard output stack and all other stacks empty. -/
theorem fold_run :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ P : Polynomial Nat,
      ∀ (i : Nat) (fs : List α),
      ∃ t ≤ P.eval (BitstringEncoding.bitEncode (i,fs)).length,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet) (BitstringEncoding.bitEncode (i,fs))) =
        some (Turing.haltList (machine core.tm core.inputAlphabet core.outputAlphabet)
          (BitstringEncoding.bitEncode (foldResult F (i,fs)))) := by
  obtain ⟨core,p,hp⟩ := loop_done F hF
  obtain ⟨q,hq⟩ := prefix_size F hF
  let P : Polynomial Nat := p+Polynomial.C 2*q+Polynomial.C 12*Polynomial.X+Polynomial.C 8
  refine ⟨core,P,?_⟩
  intro i fs
  let bits := BitstringEncoding.bitEncode i
  let tail := BitstringEncoding.bitEncode fs
  let result := BitstringEncoding.bitEncode (foldResult F (i,fs))
  let N := (BitstringEncoding.bitEncode (i,fs)).length
  obtain ⟨n,hn,hr⟩ := hp i fs
  let start := Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
    (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
      (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.delimit bits) [] [] [] [] tail)
      (Turing.initList core.tm []).stk)
  let finish := Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
    (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
      (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none result [] [] [] [] [])
      (Turing.initList core.tm []).stk)
  have he : BitstringEncoding.bitEncode (i,([] : List β)) = BitstringEncoding.delimit (BitstringEncoding.bitEncode i) := by
    change BitstringEncoding.delimit (BitstringEncoding.bitEncode i) ++ [] = _
    simp
  rw [he] at hr
  change runSteps (Source core.tm core.inputAlphabet core.outputAlphabet).step n start = some finish at hr
  obtain ⟨d,hd,hs⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    (Source core.tm core.inputAlphabet core.outputAlphabet).step (machine core.tm core.inputAlphabet core.outputAlphabet).step
    (embed core.tm core.inputAlphabet core.outputAlphabet) (terminal core.tm core.inputAlphabet core.outputAlphabet)
    (stable core.tm core.inputAlphabet core.outputAlphabet) (core_step core.tm core.inputAlphabet core.outputAlphabet)
    n start finish (by rfl) hr
  have hcount : fs.length ≤ N := by
    have hh := Shared.ComplexityBridge.CNF.list_length_le_bitEncode fs
    change fs.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode fs).length
    simp only [List.length_append]; omega
  have hbits : bits.length ≤ N := by
    change (BitstringEncoding.bitEncode i).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode fs).length
    simp only [List.length_append,BitstringEncoding.length_delimit]; omega
  have hidx := Shared.ComplexityBridge.TM2GuardAllStep.index_bits_add i fs.length
  have hguard : (BitstringEncoding.bitEncode (indexed F i fs)).length ≤ q.eval N := by
    have hh := hq i fs fs.length
    simpa [N] using hh
  have hresult : result.length ≤ 4*N+q.eval N+1 := by
    change (BitstringEncoding.delimit (BitstringEncoding.bitEncode (i+fs.length))++
      BitstringEncoding.bitEncode (indexed F i fs)).length ≤ _
    simp only [List.length_append,BitstringEncoding.length_delimit]
    dsimp [bits,N] at *
    omega
  refine ⟨(4*bits.length+3)+d+(2*result.length+3),?_,?_⟩
  · change (4*bits.length+3)+d+(2*result.length+3) ≤ P.eval N
    simp only [P,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    dsimp [N] at *
    omega
  · change runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step
      ((4*bits.length+3)+d+(2*result.length+3))
      (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet) (BitstringEncoding.delimit bits++tail)) = _
    rw [show (4*bits.length+3)+d+(2*result.length+3) =
      (4*bits.length+3)+(d+(2*result.length+3)) by omega,runSteps_add,load_run]
    change runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step
      (d+(2*result.length+3)) (embed core.tm core.inputAlphabet core.outputAlphabet start) = _
    rw [runSteps_add,hs]
    exact cleanup_run core.tm core.inputAlphabet core.outputAlphabet result

theorem foldResult_isPolyTime : ComplexityTheory.IsPolyTime (foldResult F) := by
  obtain ⟨core,p,hp⟩ := fold_run F hF
  refine ⟨{
    tm := machine core.tm core.inputAlphabet core.outputAlphabet
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := p
    outputsFun := ?_ }⟩
  intro z
  rcases z with ⟨i,fs⟩
  classical
  let t := Nat.find (hp i fs)
  have ht := (Nat.find_spec (hp i fs)).1
  have hr := (Nat.find_spec (hp i fs)).2
  refine ⟨⟨t,?_⟩,ht⟩
  rw [runSteps_iterate] at hr
  change (fun o => o.bind (machine core.tm core.inputAlphabet core.outputAlphabet).step)^[t]
    (some (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet)
      ((BitstringEncoding.bitEncode (i,fs)).map id))) =
    some (Turing.haltList (machine core.tm core.inputAlphabet core.outputAlphabet)
      ((BitstringEncoding.bitEncode (foldResult F (i,fs))).map id))
  simp only [List.map_id]
  exact hr

/-- Indexed mapping is computed by a finite TM2 within a polynomial in the
complete encoded input. The map function may itself be any certified canonical
polynomial-time function. -/
theorem indexed_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Nat × List α => indexed F p.1 p.2) := by
  have h := TM2Compose.isPolyTime_comp (foldResult F)
    (fun p : Nat × List β => p.2) (foldResult_isPolyTime F hF) TM2GuardAllStep.second_isPolyTime
  simpa [foldResult] using h

end Shared.ComplexityBridge.TM2IndexedMapLoop
