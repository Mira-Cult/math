import Shared.ComplexityBridge.TM2ContextMapIO
import Shared.ComplexityBridge.TM2GuardAllStep

set_option backward.isDefEq.respectTransparency false

/-! Generic context-preserving map using the verified finite traversal. The
item function must have an actual canonical polynomial-time TM2 witness. -/
namespace Shared.ComplexityBridge.TM2ContextMapGeneric
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

theorem item_step {κ α β : Type} [BitstringEncoding κ] [BitstringEncoding α] [BitstringEncoding β]
    (F : κ × α → β) (hF : ComplexityTheory.IsPolyTime F) :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ q : Polynomial Nat,
      ∀ (ctx : κ) (xs : List α) (x : α), x ∈ xs → ∀ acc tail : List Bool,
      ∃ t ≤ q.eval (BitstringEncoding.bitEncode (ctx,xs)).length,
        runSteps (Shared.ComplexityBridge.TM2ContextMapLoop.machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode ctx) [] [] [] acc
              (BitstringEncoding.delimit (BitstringEncoding.bitEncode x)++tail)) (Turing.initList core.tm []).stk) =
        some (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode ctx) [] [] []
            ((BitstringEncoding.delimit (BitstringEncoding.bitEncode (F (ctx,x)))).reverse++acc) tail)
            (Turing.initList core.tm []).stk) := by
  obtain ⟨core,p,hp⟩ := Shared.ComplexityBridge.TM2MapSizeBounds.context_item_run F hF
  obtain ⟨r,hr⟩ := Shared.ComplexityBridge.TM2MapSizeBounds.output_length_poly F hF
  let q : Polynomial Nat := Polynomial.C 9*Polynomial.X+p+Polynomial.C 3*r+Polynomial.C 13
  refine ⟨core,q,?_⟩
  intro ctx xs x hx acc tail
  obtain ⟨n,hn,hcore⟩ := hp ctx xs x hx
  have he : runSteps core.tm.step n
      (Turing.initList core.tm ((BitstringEncoding.delimit (BitstringEncoding.bitEncode ctx)++
        BitstringEncoding.bitEncode x).map core.inputAlphabet.symm)) =
      some (Turing.haltList core.tm ((BitstringEncoding.bitEncode (F (ctx,x))).map core.outputAlphabet.symm)) := hcore
  obtain ⟨m,hm,hs⟩ := Shared.ComplexityBridge.TM2ContextMapCall.split_call_emit core.tm core.inputAlphabet core.outputAlphabet
    (BitstringEncoding.bitEncode ctx) (BitstringEncoding.bitEncode x) (BitstringEncoding.bitEncode (F (ctx,x))) acc tail n he
  obtain ⟨d,hd,hrun⟩ := Shared.ComplexityBridge.TM2ContextMapLoop.run_to_done core.tm core.inputAlphabet core.outputAlphabet m _ _ (by rfl) hs
  refine ⟨d+1,?_,?_⟩
  · let N := (BitstringEncoding.bitEncode (ctx,xs)).length
    have hpair : (BitstringEncoding.bitEncode (ctx,x)).length ≤ N :=
      Shared.ComplexityBridge.TM2MapSizeBounds.context_element_le ctx hx
    have hctx : (BitstringEncoding.bitEncode ctx).length ≤ N := by
      change (BitstringEncoding.bitEncode ctx).length ≤
        (BitstringEncoding.delimit (BitstringEncoding.bitEncode ctx)++BitstringEncoding.bitEncode xs).length
      simp only [List.length_append,BitstringEncoding.length_delimit]; omega
    have hxsize : (BitstringEncoding.bitEncode x).length ≤ N := by
      have hh := Shared.ComplexityBridge.TM2MapSizeBounds.element_length_le hx
      change (BitstringEncoding.bitEncode x).length ≤
        (BitstringEncoding.delimit (BitstringEncoding.bitEncode ctx)++BitstringEncoding.bitEncode xs).length
      simp only [List.length_append]; omega
    have hout : (BitstringEncoding.bitEncode (F (ctx,x))).length ≤ r.eval N :=
      le_trans (hr (ctx,x)) (Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono r hpair)
    change (BitstringEncoding.delimit (BitstringEncoding.bitEncode ctx)++BitstringEncoding.bitEncode x).length ≤ N at hpair
    change d+1 ≤ q.eval N
    simp only [q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    dsimp [N] at *
    omega
  · rw [runSteps_add,hrun]
    exact Shared.ComplexityBridge.TM2ContextMapLoop.restart core.tm core.inputAlphabet core.outputAlphabet _ _ _

theorem map_loop {κ α β : Type} [BitstringEncoding κ] [BitstringEncoding α] [BitstringEncoding β]
    (F : κ × α → β) (hF : ComplexityTheory.IsPolyTime F) :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ q : Polynomial Nat,
      ∀ (ctx : κ) (xs ys : List α), (∀ x ∈ ys, x ∈ xs) → ∀ acc : List Bool,
      ∃ t ≤ ys.length*q.eval (BitstringEncoding.bitEncode (ctx,xs)).length,
        runSteps (Shared.ComplexityBridge.TM2ContextMapLoop.machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode ctx) [] [] []
              acc (BitstringEncoding.bitEncode ys)) (Turing.initList core.tm []).stk) =
        some (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode ctx) [] [] []
            ((BitstringEncoding.bitEncode (ys.map (fun x => F (ctx,x)))).reverse++acc) [])
            (Turing.initList core.tm []).stk) := by
  obtain ⟨core,q,hq⟩ := item_step F hF
  refine ⟨core,q,?_⟩
  intro ctx xs ys
  induction ys with
  | nil =>
    intro _ acc
    refine ⟨0,by simp,?_⟩
    rfl
  | cons x ys ih =>
    intro hsubset acc
    have hx : x ∈ xs := hsubset x (by simp)
    have hrest : ∀ y ∈ ys, y ∈ xs := by intro y hy; exact hsubset y (by simp [hy])
    obtain ⟨t,ht,hs⟩ := hq ctx xs x hx acc (BitstringEncoding.bitEncode ys)
    obtain ⟨u,hu,hr⟩ := ih hrest ((BitstringEncoding.delimit (BitstringEncoding.bitEncode (F (ctx,x)))).reverse++acc)
    refine ⟨t+u,?_,?_⟩
    · rw [List.length_cons,Nat.succ_mul]; omega
    · rw [runSteps_add]
      change (runSteps (Shared.ComplexityBridge.TM2ContextMapLoop.machine core.tm core.inputAlphabet core.outputAlphabet).step t
        (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode ctx) [] [] [] acc
            (BitstringEncoding.delimit (BitstringEncoding.bitEncode x)++BitstringEncoding.bitEncode ys))
            (Turing.initList core.tm []).stk)).bind _ = _
      rw [hs]
      simpa [Shared.ComplexityBridge.TM2MapSizeBounds.encode_cons,List.reverse_append,List.append_assoc] using hr

theorem map_done {κ α β : Type} [BitstringEncoding κ] [BitstringEncoding α] [BitstringEncoding β]
    (F : κ × α → β) (hF : ComplexityTheory.IsPolyTime F) :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial Nat,
      ∀ (ctx : κ) (xs : List α), ∃ t ≤ p.eval (BitstringEncoding.bitEncode (ctx,xs)).length,
        runSteps (Shared.ComplexityBridge.TM2ContextMapLoop.machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
            (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.bitEncode ctx) [] [] []
              [] (BitstringEncoding.bitEncode xs)) (Turing.initList core.tm []).stk) =
        some (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
          (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none (BitstringEncoding.bitEncode ctx) [] [] []
            (BitstringEncoding.bitEncode (xs.map (fun x => F (ctx,x)))).reverse []) (Turing.initList core.tm []).stk) := by
  obtain ⟨core,q,hq⟩ := map_loop F hF
  let p : Polynomial Nat := Polynomial.X*q+Polynomial.C 1
  refine ⟨core,p,?_⟩
  intro ctx xs
  obtain ⟨t,ht,hs⟩ := hq ctx xs xs (by simp) []
  refine ⟨t+1,?_,?_⟩
  · have hc := Shared.ComplexityBridge.CNF.list_length_le_bitEncode xs
    have hN : (BitstringEncoding.bitEncode xs).length ≤ (BitstringEncoding.bitEncode (ctx,xs)).length := by
      change (BitstringEncoding.bitEncode xs).length ≤
        (BitstringEncoding.delimit (BitstringEncoding.bitEncode ctx)++BitstringEncoding.bitEncode xs).length
      simp
    have hm := Nat.mul_le_mul_right (q.eval (BitstringEncoding.bitEncode (ctx,xs)).length) (le_trans hc hN)
    simp only [p,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega
  · rw [runSteps_add,hs]
    simpa [runSteps] using Shared.ComplexityBridge.TM2ContextMapLoop.empty_done core.tm core.inputAlphabet core.outputAlphabet _ _

def contextMap {κ α β : Type} (F : κ × α → β) (p : κ × List α) : List β :=
  p.2.map (fun x => F (p.1,x))

/-- A full finite TM2 run from the canonical `(context,list)` input to the
canonical mapped output, with input loading and cleanup charged. -/
theorem map_run {κ α β : Type} [BitstringEncoding κ] [BitstringEncoding α] [BitstringEncoding β]
    (F : κ × α → β) (hF : ComplexityTheory.IsPolyTime F) :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ P : Polynomial Nat,
      ∀ (ctx : κ) (xs : List α), ∃ t ≤ P.eval (BitstringEncoding.bitEncode (ctx,xs)).length,
        runSteps (Shared.ComplexityBridge.TM2ContextMapIO.machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Turing.initList (Shared.ComplexityBridge.TM2ContextMapIO.machine core.tm core.inputAlphabet core.outputAlphabet)
            (BitstringEncoding.bitEncode (ctx,xs))) =
        some (Turing.haltList (Shared.ComplexityBridge.TM2ContextMapIO.machine core.tm core.inputAlphabet core.outputAlphabet)
          (BitstringEncoding.bitEncode (contextMap F (ctx,xs)))) := by
  obtain ⟨core,p,hp⟩ := map_done F hF
  obtain ⟨q,hq⟩ := Shared.ComplexityBridge.TM2MapSizeBounds.context_map_sublist_size F hF
  let P : Polynomial Nat := p+q+Polynomial.C 4*Polynomial.X+Polynomial.C 5
  refine ⟨core,P,?_⟩
  intro ctx xs
  let a := BitstringEncoding.bitEncode ctx
  let tail := BitstringEncoding.bitEncode xs
  let result := BitstringEncoding.bitEncode (contextMap F (ctx,xs))
  let N := (BitstringEncoding.bitEncode (ctx,xs)).length
  obtain ⟨n,hn,hr⟩ := hp ctx xs
  let start := Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
    (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none a [] [] [] [] tail) (Turing.initList core.tm []).stk
  let finish := Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
    (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none a [] [] [] result.reverse []) (Turing.initList core.tm []).stk
  change runSteps (Shared.ComplexityBridge.TM2ContextMapIO.Source core.tm core.inputAlphabet core.outputAlphabet).step n start = some finish at hr
  obtain ⟨d,hd,hs⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    (Shared.ComplexityBridge.TM2ContextMapIO.Source core.tm core.inputAlphabet core.outputAlphabet).step
    (Shared.ComplexityBridge.TM2ContextMapIO.machine core.tm core.inputAlphabet core.outputAlphabet).step
    (Shared.ComplexityBridge.TM2ContextMapIO.embed core.tm core.inputAlphabet core.outputAlphabet)
    (Shared.ComplexityBridge.TM2ContextMapIO.terminal core.tm core.inputAlphabet core.outputAlphabet)
    (Shared.ComplexityBridge.TM2ContextMapIO.stable core.tm core.inputAlphabet core.outputAlphabet)
    (Shared.ComplexityBridge.TM2ContextMapIO.core_step core.tm core.inputAlphabet core.outputAlphabet)
    n start finish (by rfl) hr
  have ha : a.length ≤ N := by
    change (BitstringEncoding.bitEncode ctx).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode ctx)++BitstringEncoding.bitEncode xs).length
    simp only [List.length_append,BitstringEncoding.length_delimit]; omega
  have hout : result.length ≤ q.eval N := by
    have hh := hq ctx xs xs (List.Sublist.refl xs)
    simpa [result,contextMap,N] using hh
  refine ⟨(3*a.length+2)+d+(a.length+result.length+3),?_,?_⟩
  · change (3*a.length+2)+d+(a.length+result.length+3) ≤ P.eval N
    simp only [P,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    dsimp [N] at *; omega
  · change runSteps (Shared.ComplexityBridge.TM2ContextMapIO.machine core.tm core.inputAlphabet core.outputAlphabet).step
      ((3*a.length+2)+d+(a.length+result.length+3))
      (Turing.initList (Shared.ComplexityBridge.TM2ContextMapIO.machine core.tm core.inputAlphabet core.outputAlphabet)
        (BitstringEncoding.delimit a++tail)) = _
    rw [show (3*a.length+2)+d+(a.length+result.length+3) =
      (3*a.length+2)+(d+(a.length+result.length+3)) by omega,runSteps_add,Shared.ComplexityBridge.TM2ContextMapIO.load_run]
    change runSteps (Shared.ComplexityBridge.TM2ContextMapIO.machine core.tm core.inputAlphabet core.outputAlphabet).step
      (d+(a.length+result.length+3)) (Shared.ComplexityBridge.TM2ContextMapIO.embed core.tm core.inputAlphabet core.outputAlphabet start) = _
    rw [runSteps_add,hs]
    have hc := Shared.ComplexityBridge.TM2ContextMapIO.cleanup_run core.tm core.inputAlphabet core.outputAlphabet a result.reverse
    simpa [finish,List.reverse_reverse,List.length_reverse] using hc

/-- Mapping a canonically polynomial-time context/item function over a list is
canonically polynomial time; this constructs a finite machine and charges the
complete run, including all context copies, framing, and output cleanup. -/
theorem contextMap_isPolyTime {κ α β : Type} [BitstringEncoding κ] [BitstringEncoding α] [BitstringEncoding β]
    (F : κ × α → β) (hF : ComplexityTheory.IsPolyTime F) :
    ComplexityTheory.IsPolyTime (contextMap F) := by
  obtain ⟨core,p,hp⟩ := map_run F hF
  refine ⟨{
    tm := Shared.ComplexityBridge.TM2ContextMapIO.machine core.tm core.inputAlphabet core.outputAlphabet
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := p
    outputsFun := ?_ }⟩
  intro z
  rcases z with ⟨ctx,xs⟩
  classical
  let t := Nat.find (hp ctx xs)
  have ht := (Nat.find_spec (hp ctx xs)).1
  have hr := (Nat.find_spec (hp ctx xs)).2
  refine ⟨⟨t,?_⟩,ht⟩
  rw [runSteps_iterate] at hr
  change (fun o => o.bind (Shared.ComplexityBridge.TM2ContextMapIO.machine core.tm core.inputAlphabet core.outputAlphabet).step)^[t]
    (some (Turing.initList (Shared.ComplexityBridge.TM2ContextMapIO.machine core.tm core.inputAlphabet core.outputAlphabet)
      ((BitstringEncoding.bitEncode (ctx,xs)).map id))) =
    some (Turing.haltList (Shared.ComplexityBridge.TM2ContextMapIO.machine core.tm core.inputAlphabet core.outputAlphabet)
      ((BitstringEncoding.bitEncode (contextMap F (ctx,xs))).map id))
  simp only [List.map_id]
  exact hr


/-- Ordinary list map is a specialization: duplicate the input list as
context and map a function that ignores that context. -/
theorem listMap_isPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (F : α → β) (hF : ComplexityTheory.IsPolyTime F) :
    ComplexityTheory.IsPolyTime (fun xs : List α => xs.map F) := by
  let get : List α × α → α := fun p => p.2
  let ignore : List α × α → β := fun p => F p.2
  have hg : ComplexityTheory.IsPolyTime get := Shared.ComplexityBridge.TM2GuardAllStep.second_isPolyTime
  have hi : ComplexityTheory.IsPolyTime ignore := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp get F hg hF
  let dup : List α → List α × List α := fun xs => (xs,xs)
  have hd : ComplexityTheory.IsPolyTime dup := Shared.ComplexityBridge.TM2GenericDiagonal.diagonal_isPolyTime
  have hm := contextMap_isPolyTime ignore hi
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp dup (contextMap ignore) hd hm
  simpa [dup,ignore,contextMap] using h

end Shared.ComplexityBridge.TM2ContextMapGeneric
