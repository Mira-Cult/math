import Shared.ComplexityBridge.TM2ContextMapCall

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Repeat the proved guard-item segment by returning the emitter's done
label to the item parser. This module starts with explicitly prepared stacks;
whole-input loading and final output cleanup are separate obligations. -/
namespace Shared.ComplexityBridge.TM2ContextMapLoop
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.CNF Shared.ComplexityBridge.CNFDisjunction

def program (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) :
    Shared.ComplexityBridge.TM2ContextMapCall.Label f → Stmt (Shared.ComplexityBridge.TM2ContextMapCall.Alphabet f) (Shared.ComplexityBridge.TM2ContextMapCall.Label f) (Shared.ComplexityBridge.TM2ContextMapCall.State f)
  | .inl (.inl .done) => .load (fun _ => .inl none) (.goto (fun _ => .inl (.inr .header)))
  | l => Shared.ComplexityBridge.TM2ContextMapCall.program f inp out l

def machine (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) : Turing.FinTM2 :=
  { Shared.ComplexityBridge.TM2ContextMapCall.machine f inp out with m := program f inp out }

def terminal (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (q : (Shared.ComplexityBridge.TM2ContextMapCall.machine f inp out).Cfg) : Prop := q.l = some (.inl (.inl .done))
noncomputable instance (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) :
    DecidablePred (terminal f inp out) := fun _ => Classical.propDecidable _

theorem stable (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (q : (Shared.ComplexityBridge.TM2ContextMapCall.machine f inp out).Cfg) (h : terminal f inp out q) : (Shared.ComplexityBridge.TM2ContextMapCall.machine f inp out).step q = some q := by
  cases q with
  | mk l v st => change l = some (.inl (.inl .done)) at h; subst l; rfl

theorem simulate (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (q : (Shared.ComplexityBridge.TM2ContextMapCall.machine f inp out).Cfg) (h : ¬ terminal f inp out q) :
    (machine f inp out).step q = (Shared.ComplexityBridge.TM2ContextMapCall.machine f inp out).step q := by
  cases q with
  | mk l v st =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | inl l =>
        cases l with
        | inl l =>
          cases l with
          | done => exact False.elim (h rfl)
          | scanPayload | restorePayload | scanContext | restoreContext | ready | emit => rfl
        | inr l => cases l <;> rfl
      | inr l => cases l with
        | inl l => cases l <;> rfl
        | inr l => rfl

theorem run_to_done (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (n : Nat) (start finish : (Shared.ComplexityBridge.TM2ContextMapCall.machine f inp out).Cfg) (hf : terminal f inp out finish)
    (hr : runSteps (Shared.ComplexityBridge.TM2ContextMapCall.machine f inp out).step n start = some finish) :
    ∃ t ≤ n, runSteps (machine f inp out).step t start = some finish := by
  exact Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    (Shared.ComplexityBridge.TM2ContextMapCall.machine f inp out).step (machine f inp out).step id (terminal f inp out)
    (stable f inp out) (fun q h => by simpa using simulate f inp out q h) n start finish hf hr

theorem restart (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx acc tail : List Bool) :
    (machine f inp out).step
      (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inl .done) none ctx [] [] [] acc tail) (Turing.haltList f []).stk) =
      some (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] acc tail) (Turing.initList f []).stk) := by
  have h : (Turing.haltList f []).stk = (Turing.initList f []).stk := by
    rw [Shared.ComplexityBridge.TM2Compose.haltStacks_empty,Shared.ComplexityBridge.TM2Compose.initStacks_empty]
  rw [← h]
  rfl

/-- One restarted guard step is finite, because the item computation is the
proved terminating guard evaluator. -/
theorem guard_step :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial Nat,
      ∀ (i : Nat) (formula : Formula) (clause : Clause), clause ∈ formula → ∀ acc tail : List Bool,
      ∃ t ≤ 5*(BitstringEncoding.bitEncode clause).length + 2*(BitstringEncoding.bitEncode i).length + 6 +
          2*(BitstringEncoding.bitEncode (i,clause)).length + 3 +
          p.eval (BitstringEncoding.bitEncode (i,formula)).length +
          3*(BitstringEncoding.bitEncode (guardClause i clause)).length + 4,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode i) [] [] [] acc
            (BitstringEncoding.delimit (BitstringEncoding.bitEncode clause)++tail)) (Turing.initList core.tm []).stk) =
        some (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode i) [] [] []
          ((BitstringEncoding.delimit (BitstringEncoding.bitEncode (guardClause i clause))).reverse++acc) tail)
          (Turing.initList core.tm []).stk) := by
  obtain ⟨core,p,hp⟩ := Shared.ComplexityBridge.TM2ContextMapCall.guard_item_segment
  refine ⟨core,p,?_⟩
  intro i formula clause hc acc tail
  obtain ⟨n,hn,hr⟩ := hp i formula clause hc acc tail
  obtain ⟨d,hd,hs⟩ := run_to_done core.tm core.inputAlphabet core.outputAlphabet n _ _ (by rfl) hr
  refine ⟨d+1,by omega,?_⟩
  rw [runSteps_add,hs]
  exact restart core.tm core.inputAlphabet core.outputAlphabet _ _ _


/-- A single polynomial bounds each restarted guard segment in the encoded
length of the original index/formula request. -/
theorem guard_step_uniform :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ q : Polynomial Nat,
      ∀ (i : Nat) (formula : Formula) (clause : Clause), clause ∈ formula → ∀ acc tail : List Bool,
      ∃ t ≤ q.eval (BitstringEncoding.bitEncode (i,formula)).length,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode i) [] [] [] acc
              (BitstringEncoding.delimit (BitstringEncoding.bitEncode clause)++tail)) (Turing.initList core.tm []).stk) =
        some (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode i) [] [] []
            ((BitstringEncoding.delimit (BitstringEncoding.bitEncode (guardClause i clause))).reverse++acc) tail)
            (Turing.initList core.tm []).stk) := by
  obtain ⟨core,p,hp⟩ := guard_step
  obtain ⟨r,hr⟩ := Shared.ComplexityBridge.TM2MapSizeBounds.output_length_poly
    (fun z : Nat × Clause => guardClause z.1 z.2)
    Shared.ComplexityBridge.TM2PairSwap.guardClause_isPolyTime
  let q : Polynomial Nat := Polynomial.C 9*Polynomial.X+p+Polynomial.C 3*r+Polynomial.C 13
  refine ⟨core,q,?_⟩
  intro i formula clause hc acc tail
  obtain ⟨t,ht,hs⟩ := hp i formula clause hc acc tail
  refine ⟨t,?_,hs⟩
  let N := (BitstringEncoding.bitEncode (i,formula)).length
  have hpair : (BitstringEncoding.bitEncode (i,clause)).length ≤ N :=
    Shared.ComplexityBridge.TM2MapSizeBounds.context_element_le i hc
  have hidx : (BitstringEncoding.bitEncode i).length ≤ N := by
    change (BitstringEncoding.bitEncode i).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode formula).length
    simp only [List.length_append,BitstringEncoding.length_delimit]
    omega
  have hclause : (BitstringEncoding.bitEncode clause).length ≤ N := by
    have hh := Shared.ComplexityBridge.TM2MapSizeBounds.element_length_le hc
    change (BitstringEncoding.bitEncode clause).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode formula).length
    simp only [List.length_append]
    omega
  have hout : (BitstringEncoding.bitEncode (guardClause i clause)).length ≤ r.eval N :=
    le_trans (hr (i,clause)) (Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono r hpair)
  change t ≤ q.eval N
  simp only [q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  dsimp [N] at *
  omega


/-- The same finite machine processes every clause in order. It starts with
explicit context and list stacks and leaves the mapped encoding in reverse
on the accumulator. The total bound counts one bounded segment per clause. -/
theorem guard_loop :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ q : Polynomial Nat,
      ∀ (i : Nat) (formula xs : Formula), (∀ c ∈ xs, c ∈ formula) → ∀ acc : List Bool,
      ∃ t ≤ xs.length*q.eval (BitstringEncoding.bitEncode (i,formula)).length,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode i) [] [] []
              acc (BitstringEncoding.bitEncode xs)) (Turing.initList core.tm []).stk) =
        some (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode i) [] [] []
            ((BitstringEncoding.bitEncode (guardFormula i xs)).reverse++acc) [])
            (Turing.initList core.tm []).stk) := by
  obtain ⟨core,q,hq⟩ := guard_step_uniform
  refine ⟨core,q,?_⟩
  intro i formula xs
  induction xs with
  | nil =>
    intro _ acc
    refine ⟨0,by simp,?_⟩
    rfl
  | cons clause xs ih =>
    intro hsubset acc
    have hc : clause ∈ formula := hsubset clause (by simp)
    have hrest : ∀ c ∈ xs, c ∈ formula := by
      intro c hc; exact hsubset c (by simp [hc])
    obtain ⟨t,ht,hs⟩ := hq i formula clause hc acc (BitstringEncoding.bitEncode xs)
    obtain ⟨u,hu,hr⟩ := ih hrest ((BitstringEncoding.delimit (BitstringEncoding.bitEncode (guardClause i clause))).reverse++acc)
    refine ⟨t+u,?_,?_⟩
    · rw [List.length_cons,Nat.succ_mul]
      omega
    · rw [runSteps_add]
      change (runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
        (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode i) [] [] [] acc
            (BitstringEncoding.delimit (BitstringEncoding.bitEncode clause)++BitstringEncoding.bitEncode xs))
            (Turing.initList core.tm []).stk)).bind _ = _
      rw [hs]
      simpa [guardFormula,Shared.ComplexityBridge.TM2MapSizeBounds.encode_cons,List.reverse_append,List.append_assoc] using hr


/-- Full formula traversal with an explicit polynomial in the canonical
encoded request size. Input loading and final stack cleanup remain outside
this theorem. -/
theorem guard_formula_loop :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial Nat,
      ∀ (i : Nat) (formula : Formula),
      ∃ t ≤ p.eval (BitstringEncoding.bitEncode (i,formula)).length,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode i) [] [] []
              [] (BitstringEncoding.bitEncode formula)) (Turing.initList core.tm []).stk) =
        some (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode i) [] [] []
            (BitstringEncoding.bitEncode (guardFormula i formula)).reverse [])
            (Turing.initList core.tm []).stk) := by
  obtain ⟨core,q,hq⟩ := guard_loop
  refine ⟨core,Polynomial.X*q,?_⟩
  intro i formula
  obtain ⟨t,ht,hs⟩ := hq i formula formula (by simp) []
  refine ⟨t,?_,by simpa using hs⟩
  have hc := Shared.ComplexityBridge.CNF.list_length_le_bitEncode formula
  have hN : (BitstringEncoding.bitEncode formula).length ≤ (BitstringEncoding.bitEncode (i,formula)).length := by
    change (BitstringEncoding.bitEncode formula).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode i)++BitstringEncoding.bitEncode formula).length
    simp
  have hm := Nat.mul_le_mul_right (q.eval (BitstringEncoding.bitEncode (i,formula)).length) (le_trans hc hN)
  simp only [Polynomial.eval_mul,Polynomial.eval_X]
  omega

theorem empty_done (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (ctx acc : List Bool) :
    (machine f inp out).step
      (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
        (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] acc []) (Turing.initList f []).stk) =
    some (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
      (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none ctx [] [] [] acc []) (Turing.initList f []).stk) := by
  let q := Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed f
    (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] acc []) (Turing.initList f []).stk
  have hsim := simulate f inp out q (by intro h; cases h)
  have hsrc := Shared.ComplexityBridge.TM2ContextMapCall.src_step f inp out (Turing.initList f []).stk
    (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none ctx [] [] [] acc []) (by intro h; cases h)
  rw [Shared.ComplexityBridge.TM2ContextMapSplit.header_nil] at hsrc
  exact hsim.trans hsrc


/-- The traversal also reaches the parser's distinct empty-input done label,
with the mapped output still on the reverse accumulator. -/
theorem guard_formula_done :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial Nat,
      ∀ (i : Nat) (formula : Formula),
      ∃ t ≤ p.eval (BitstringEncoding.bitEncode (i,formula)).length,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode i) [] [] []
              [] (BitstringEncoding.bitEncode formula)) (Turing.initList core.tm []).stk) =
        some (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none (BitstringEncoding.bitEncode i) [] [] []
            (BitstringEncoding.bitEncode (guardFormula i formula)).reverse [])
            (Turing.initList core.tm []).stk) := by
  obtain ⟨core,p,hp⟩ := guard_formula_loop
  refine ⟨core,p+Polynomial.C 1,?_⟩
  intro i formula
  obtain ⟨t,ht,hs⟩ := hp i formula
  refine ⟨t+1,?_,?_⟩
  · simp only [Polynomial.eval_add,Polynomial.eval_C]; omega
  · rw [runSteps_add,hs]
    exact empty_done core.tm core.inputAlphabet core.outputAlphabet _ _

end Shared.ComplexityBridge.TM2ContextMapLoop
