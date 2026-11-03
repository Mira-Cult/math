import Shared.ComplexityBridge.TM2FoldHandoff

set_option backward.isDefEq.respectTransparency false

/-! General finite list-fold interface using the concrete TM2 fold handoff.
The evaluator run and the size bounds are explicit hypotheses: no arbitrary
Lean function is treated as an executable machine. -/
namespace Shared.ComplexityBridge.TM2PolynomialFold
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

def fold {σ α : Type} (step : σ × α → σ) (init : σ) (xs : List α) : σ :=
  xs.foldl (fun s a => step (s,a)) init

theorem fold_append_singleton {σ α : Type} (step : σ × α → σ) (init : σ) (xs : List α) (x : α) :
    fold step init (xs++[x]) = step (fold step init xs,x) := by simp [fold,List.foldl_append]

/-- Run a finite TM2 fold on explicitly populated stacks. Every prefix must
provide an actual bounded evaluator run and explicit bounds on all serialized
inputs and outputs. The result counts every split, transfer, framing, and
restart operation, as well as the item-machine execution. -/
theorem loop_run {σ α : Type} [BitstringEncoding σ] [BitstringEncoding α]
    (step : σ × α → σ) (core : Turing.TM2ComputableAux Bool Bool) (init : σ) (xs : List α) (B : Nat)
    (hstep : ∀ pref (item : α) tail, xs = pref++item::tail →
      let state := fold step init pref
      ∃ n ≤ B,
        runSteps core.tm.step n
          (Turing.initList core.tm ((BitstringEncoding.bitEncode (state,item)).map core.inputAlphabet.symm)) =
          some (Turing.haltList core.tm ((BitstringEncoding.bitEncode (step (state,item))).map core.outputAlphabet.symm)) ∧
        (BitstringEncoding.bitEncode state).length ≤ B ∧
        (BitstringEncoding.bitEncode item).length ≤ B ∧
        (BitstringEncoding.bitEncode (state,item)).length ≤ B ∧
        (BitstringEncoding.bitEncode (step (state,item))).length ≤ B) :
    ∃ t ≤ xs.length*(16*B+16),
      runSteps (Shared.ComplexityBridge.TM2FoldHandoff.machine core.tm core.inputAlphabet core.outputAlphabet).step t
        (Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
              (BitstringEncoding.bitEncode init) [] [] [] [] (BitstringEncoding.bitEncode xs)) (Turing.initList core.tm []).stk)) =
      some (Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
        (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
            (BitstringEncoding.bitEncode (fold step init xs)) [] [] [] [] []) (Turing.initList core.tm []).stk)) := by
  have walk : ∀ (rest pref : List α), xs = pref++rest →
      ∃ t ≤ rest.length*(16*B+16),
        runSteps (Shared.ComplexityBridge.TM2FoldHandoff.machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
            (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
              (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
                (BitstringEncoding.bitEncode (fold step init pref)) [] [] [] [] (BitstringEncoding.bitEncode rest))
              (Turing.initList core.tm []).stk)) =
        some (Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
              (BitstringEncoding.bitEncode (fold step init xs)) [] [] [] [] []) (Turing.initList core.tm []).stk)) := by
    intro rest
    induction rest with
    | nil =>
      intro pref heq
      have hp : xs = pref := by simpa using heq
      subst xs
      refine ⟨0,by simp,?_⟩
      have he : BitstringEncoding.bitEncode ([] : List α) = [] := rfl
      simp [runSteps,he]
    | cons item rest ih =>
      intro pref heq
      obtain ⟨n,hn,hr,hold,hitem,hpair,hout⟩ := hstep pref item rest heq
      have he : runSteps core.tm.step n
          (Turing.initList core.tm ((BitstringEncoding.delimit (BitstringEncoding.bitEncode (fold step init pref))++
            BitstringEncoding.bitEncode item).map core.inputAlphabet.symm)) =
          some (Turing.haltList core.tm ((BitstringEncoding.bitEncode (step (fold step init pref,item))).map core.outputAlphabet.symm)) := hr
      obtain ⟨t,ht,hs⟩ := Shared.ComplexityBridge.TM2FoldHandoff.step_run core.tm core.inputAlphabet core.outputAlphabet
        (BitstringEncoding.bitEncode (fold step init pref)) (BitstringEncoding.bitEncode item)
        (BitstringEncoding.bitEncode (step (fold step init pref,item))) (BitstringEncoding.bitEncode rest) n he
      have hpair' : (BitstringEncoding.delimit (BitstringEncoding.bitEncode (fold step init pref))++
          BitstringEncoding.bitEncode item).length ≤ B := hpair
      have hbound : t ≤ 16*B+16 := by omega
      have hnext : xs = (pref++[item])++rest := by simpa [List.append_assoc] using heq
      obtain ⟨u,hu,htail⟩ := ih (pref++[item]) hnext
      refine ⟨t+u,?_,?_⟩
      · rw [List.length_cons,Nat.succ_mul]; omega
      · rw [runSteps_add]
        change (runSteps (Shared.ComplexityBridge.TM2FoldHandoff.machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
            (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
              (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
                (BitstringEncoding.bitEncode (fold step init pref)) [] [] [] []
                (BitstringEncoding.delimit (BitstringEncoding.bitEncode item)++BitstringEncoding.bitEncode rest))
                (Turing.initList core.tm []).stk))).bind _ = _
        rw [hs]
        simpa [fold_append_singleton] using htail
  obtain ⟨t,ht,hr⟩ := walk xs [] (by simp)
  exact ⟨t,ht,by simpa [fold] using hr⟩

/-- On empty input the parser reaches its distinct done state in one more
step, without changing the final serialized fold state. -/
theorem loop_done {σ α : Type} [BitstringEncoding σ] [BitstringEncoding α]
    (step : σ × α → σ) (core : Turing.TM2ComputableAux Bool Bool) (init : σ) (xs : List α) (B : Nat)
    (hstep : ∀ pref (item : α) tail, xs = pref++item::tail →
      let state := fold step init pref
      ∃ n ≤ B,
        runSteps core.tm.step n
          (Turing.initList core.tm ((BitstringEncoding.bitEncode (state,item)).map core.inputAlphabet.symm)) =
          some (Turing.haltList core.tm ((BitstringEncoding.bitEncode (step (state,item))).map core.outputAlphabet.symm)) ∧
        (BitstringEncoding.bitEncode state).length ≤ B ∧
        (BitstringEncoding.bitEncode item).length ≤ B ∧
        (BitstringEncoding.bitEncode (state,item)).length ≤ B ∧
        (BitstringEncoding.bitEncode (step (state,item))).length ≤ B) :
    ∃ t ≤ xs.length*(16*B+16)+1,
      runSteps (Shared.ComplexityBridge.TM2FoldHandoff.machine core.tm core.inputAlphabet core.outputAlphabet).step t
        (Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
              (BitstringEncoding.bitEncode init) [] [] [] [] (BitstringEncoding.bitEncode xs)) (Turing.initList core.tm []).stk)) =
      some (Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
        (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none
            (BitstringEncoding.bitEncode (fold step init xs)) [] [] [] [] []) (Turing.initList core.tm []).stk)) := by
  obtain ⟨t,ht,hr⟩ := loop_run step core init xs B hstep
  refine ⟨t+1,by omega,?_⟩
  rw [runSteps_add,hr]
  exact Shared.ComplexityBridge.TM2FoldHandoff.empty_done core.tm core.inputAlphabet core.outputAlphabet _

/-- A uniform polynomial bound on item executions and serialized prefix
states yields a uniform polynomial bound for the actual finite fold loop.
The bound is measured in the full canonical `(initial state, list)` input. -/
theorem loop_polynomial {σ α : Type} [BitstringEncoding σ] [BitstringEncoding α]
    (step : σ × α → σ) (core : Turing.TM2ComputableAux Bool Bool) (q : Polynomial Nat)
    (hstep : ∀ (init : σ) (xs pref : List α) (item : α) (tail : List α), xs = pref++item::tail →
      let state := fold step init pref
      let B := q.eval (BitstringEncoding.bitEncode (init,xs)).length
      ∃ n ≤ B,
        runSteps core.tm.step n
          (Turing.initList core.tm ((BitstringEncoding.bitEncode (state,item)).map core.inputAlphabet.symm)) =
          some (Turing.haltList core.tm ((BitstringEncoding.bitEncode (step (state,item))).map core.outputAlphabet.symm)) ∧
        (BitstringEncoding.bitEncode state).length ≤ B ∧
        (BitstringEncoding.bitEncode item).length ≤ B ∧
        (BitstringEncoding.bitEncode (state,item)).length ≤ B ∧
        (BitstringEncoding.bitEncode (step (state,item))).length ≤ B) :
    ∃ p : Polynomial Nat, ∀ (init : σ) (xs : List α),
      ∃ t ≤ p.eval (BitstringEncoding.bitEncode (init,xs)).length,
        runSteps (Shared.ComplexityBridge.TM2FoldHandoff.machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
            (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
              (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none
                (BitstringEncoding.bitEncode init) [] [] [] [] (BitstringEncoding.bitEncode xs)) (Turing.initList core.tm []).stk)) =
        some (Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none
              (BitstringEncoding.bitEncode (fold step init xs)) [] [] [] [] []) (Turing.initList core.tm []).stk)) := by
  let p : Polynomial Nat := Polynomial.X*(Polynomial.C 16*q+Polynomial.C 16)+Polynomial.C 1
  refine ⟨p,?_⟩
  intro init xs
  let N := (BitstringEncoding.bitEncode (init,xs)).length
  obtain ⟨t,ht,hr⟩ := loop_done step core init xs (q.eval N) (hstep init xs)
  refine ⟨t,?_,hr⟩
  have hc : xs.length ≤ N := by
    have hh := Shared.ComplexityBridge.CNF.list_length_le_bitEncode xs
    change xs.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode init)++BitstringEncoding.bitEncode xs).length
    simp only [List.length_append]
    omega
  have hm := Nat.mul_le_mul_right (16*q.eval N+16) hc
  change t ≤ p.eval N
  simp only [p,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  omega

end Shared.ComplexityBridge.TM2PolynomialFold
