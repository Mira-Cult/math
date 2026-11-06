import Shared.ComplexityBridge.TM2PairSwap

set_option backward.isDefEq.respectTransparency false

/-! Quantitative encoded-size bounds for a context-preserving list map.
These bounds use actual finite TM2 executions, but do not construct a map
machine or prove its runtime. -/
namespace Shared.ComplexityBridge.TM2MapSizeBounds
open Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

/-- The output size of any canonical polynomial-time function is polynomial
in its full encoded input size, by the finite machine's push bound. -/
theorem output_length_poly {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (F : α → β) (hF : ComplexityTheory.IsPolyTime F) :
    ∃ p : Polynomial Nat, ∀ x,
      (BitstringEncoding.bitEncode (F x)).length ≤ p.eval (BitstringEncoding.bitEncode x).length := by
  rcases hF with ⟨hF⟩
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound hF.tm
  let p : Polynomial Nat := Polynomial.X + hF.time * Polynomial.C D
  refine ⟨p,?_⟩
  intro x
  let r := hF.outputsFun x
  let n := r.steps
  have hr : runSteps hF.tm.step n (Turing.initList hF.tm ((BitstringEncoding.bitEncode x).map hF.inputAlphabet.symm)) =
      some (Turing.haltList hF.tm ((BitstringEncoding.bitEncode (F x)).map hF.outputAlphabet.symm)) := by
    rw [runSteps_iterate]
    exact r.evals_in_steps
  have hn : n ≤ hF.time.eval (BitstringEncoding.bitEncode x).length := r.steps_le_m
  have hs := Shared.ComplexityBridge.TM2GenericStackBound.run_from_input_length hF.tm
    ((BitstringEncoding.bitEncode x).map hF.inputAlphabet.symm) n
    (Turing.haltList hF.tm ((BitstringEncoding.bitEncode (F x)).map hF.outputAlphabet.symm)) hr hF.tm.k₁
  have hsize : (BitstringEncoding.bitEncode (F x)).length ≤ (BitstringEncoding.bitEncode x).length + n*D := by
    simpa [Turing.haltList,D] using hs
  have hm := Nat.mul_le_mul_right D hn
  change (BitstringEncoding.bitEncode (F x)).length ≤ p.eval (BitstringEncoding.bitEncode x).length
  simp only [p,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  omega

theorem encode_cons {α : Type} [BitstringEncoding α] (x : α) (xs : List α) :
    BitstringEncoding.bitEncode (x::xs) = BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++
      BitstringEncoding.bitEncode xs := rfl

theorem element_length_le {α : Type} [BitstringEncoding α] {x : α} {xs : List α} (h : x ∈ xs) :
    (BitstringEncoding.bitEncode x).length ≤ (BitstringEncoding.bitEncode xs).length := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    rw [encode_cons,List.length_append,BitstringEncoding.length_delimit]
    rcases List.mem_cons.mp h with he | ht
    · subst y; omega
    · have hh := ih ht; omega

theorem context_element_le {κ α : Type} [BitstringEncoding κ] [BitstringEncoding α]
    (ctx : κ) {x : α} {xs : List α} (h : x ∈ xs) :
    (BitstringEncoding.bitEncode (ctx,x)).length ≤ (BitstringEncoding.bitEncode (ctx,xs)).length := by
  change (BitstringEncoding.delimit (BitstringEncoding.bitEncode ctx) ++ BitstringEncoding.bitEncode x).length ≤
    (BitstringEncoding.delimit (BitstringEncoding.bitEncode ctx) ++ BitstringEncoding.bitEncode xs).length
  simp only [List.length_append]
  exact Nat.add_le_add_left (element_length_le h) _

theorem map_encoding_bound {α β : Type} [BitstringEncoding β]
    (F : α → β) (xs : List α) (B : Nat)
    (h : ∀ x ∈ xs, (BitstringEncoding.bitEncode (F x)).length ≤ B) :
    (BitstringEncoding.bitEncode (xs.map F)).length ≤ xs.length*(2*B+1) := by
  induction xs with
  | nil =>
    have he : BitstringEncoding.bitEncode ([] : List β) = [] := rfl
    simp [he]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ xs, (BitstringEncoding.bitEncode (F y)).length ≤ B := by
      intro y hy; exact h y (by simp [hy])
    have hh := ih ht
    rw [List.map_cons,encode_cons,List.length_append,BitstringEncoding.length_delimit,List.length_cons]
    have he : (xs.length+1)*(2*B+1) = xs.length*(2*B+1)+(2*B+1) := by ring
    rw [he]
    omega

/-- Uniform bound for mapping a binary function over a sublist while
preserving the same context. The polynomial is measured in the *whole*
encoded `(context, original list)` input. -/
theorem context_map_sublist_size {κ α β : Type} [BitstringEncoding κ] [BitstringEncoding α] [BitstringEncoding β]
    (F : κ × α → β) (hF : ComplexityTheory.IsPolyTime F) :
    ∃ q : Polynomial Nat, ∀ (ctx : κ) (xs ys : List α), ys.Sublist xs →
      (BitstringEncoding.bitEncode (ys.map (fun x => F (ctx,x)))).length ≤
        q.eval (BitstringEncoding.bitEncode (ctx,xs)).length := by
  obtain ⟨p,hp⟩ := output_length_poly F hF
  let q : Polynomial Nat := Polynomial.X*(Polynomial.C 2*p+Polynomial.C 1)
  refine ⟨q,?_⟩
  intro ctx xs ys hsub
  let N := (BitstringEncoding.bitEncode (ctx,xs)).length
  have heach : ∀ x ∈ ys, (BitstringEncoding.bitEncode (F (ctx,x))).length ≤ p.eval N := by
    intro x hx
    have hm : x ∈ xs := hsub.subset hx
    have hsize : (BitstringEncoding.bitEncode (ctx,x)).length ≤ N := context_element_le ctx hm
    exact le_trans (hp (ctx,x)) (Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono p hsize)
  have hmap := map_encoding_bound (fun x => F (ctx,x)) ys (p.eval N) heach
  have hcount : ys.length ≤ N := by
    have h₁ : ys.length ≤ xs.length := hsub.length_le
    have h₂ := Shared.ComplexityBridge.CNF.list_length_le_bitEncode xs
    have h₃ : (BitstringEncoding.bitEncode xs).length ≤ N := by
      change (BitstringEncoding.bitEncode xs).length ≤
        (BitstringEncoding.delimit (BitstringEncoding.bitEncode ctx) ++ BitstringEncoding.bitEncode xs).length
      simp
    omega
  have hm := Nat.mul_le_mul_right (2*p.eval N+1) hcount
  change (BitstringEncoding.bitEncode (ys.map (fun x => F (ctx,x)))).length ≤ q.eval N
  simp only [q,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X]
  omega

/-- One fixed finite machine handles every item of every input list with a
clock polynomial in the whole context-and-list encoding. This bounds each
individual execution, not the loop or its data movement. -/
theorem context_item_run {κ α β : Type} [BitstringEncoding κ] [BitstringEncoding α] [BitstringEncoding β]
    (F : κ × α → β) (hF : ComplexityTheory.IsPolyTime F) :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial Nat,
      ∀ (ctx : κ) (xs : List α) (x : α), x ∈ xs →
        ∃ n ≤ p.eval (BitstringEncoding.bitEncode (ctx,xs)).length,
          runSteps core.tm.step n
            (Turing.initList core.tm ((BitstringEncoding.bitEncode (ctx,x)).map core.inputAlphabet.symm)) =
          some (Turing.haltList core.tm ((BitstringEncoding.bitEncode (F (ctx,x))).map core.outputAlphabet.symm)) := by
  rcases hF with ⟨hF⟩
  refine ⟨hF.toTM2ComputableAux,hF.time,?_⟩
  intro ctx xs x hx
  let r := hF.outputsFun (ctx,x)
  refine ⟨r.steps,?_,?_⟩
  · exact le_trans r.steps_le_m
      (Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono hF.time (context_element_le ctx hx))
  · rw [runSteps_iterate]
    exact r.evals_in_steps

/-- In particular, every partially processed guarded formula has a uniform
polynomial serialized-size bound in the encoded index and original formula. -/
theorem guardFormula_prefix_size :
    ∃ q : Polynomial Nat, ∀ (i : Nat) (f : Shared.ComplexityBridge.CNF.Formula) (k : Nat),
      (BitstringEncoding.bitEncode (Shared.ComplexityBridge.CNFDisjunction.guardFormula i (f.take k))).length ≤
        q.eval (BitstringEncoding.bitEncode (i,f)).length := by
  obtain ⟨q,hq⟩ := context_map_sublist_size
    (fun p : Nat × Shared.ComplexityBridge.CNF.Clause =>
      Shared.ComplexityBridge.CNFDisjunction.guardClause p.1 p.2)
    Shared.ComplexityBridge.TM2PairSwap.guardClause_isPolyTime
  refine ⟨q,?_⟩
  intro i f k
  simpa [Shared.ComplexityBridge.CNFDisjunction.guardFormula] using hq i f (f.take k) (List.take_sublist k f)

/-- The guard-clause machine has one uniform per-clause clock in the full
encoded input size of the corresponding guarded-formula request. -/
theorem guardFormula_item_run :
    ∃ core : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial Nat,
      ∀ (i : Nat) (f : Shared.ComplexityBridge.CNF.Formula) (c : Shared.ComplexityBridge.CNF.Clause), c ∈ f →
        ∃ n ≤ p.eval (BitstringEncoding.bitEncode (i,f)).length,
          runSteps core.tm.step n
            (Turing.initList core.tm ((BitstringEncoding.bitEncode (i,c)).map core.inputAlphabet.symm)) =
          some (Turing.haltList core.tm ((BitstringEncoding.bitEncode
            (Shared.ComplexityBridge.CNFDisjunction.guardClause i c)).map core.outputAlphabet.symm)) :=
  context_item_run _ Shared.ComplexityBridge.TM2PairSwap.guardClause_isPolyTime

end Shared.ComplexityBridge.TM2MapSizeBounds
