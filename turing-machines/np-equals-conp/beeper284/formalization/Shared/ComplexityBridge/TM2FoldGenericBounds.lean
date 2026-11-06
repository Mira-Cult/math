import Shared.ComplexityBridge.TM2FoldGenericIO
import Shared.ComplexityBridge.TM2MapSizeBounds

/-! Promote the generic fold wrapper to a convenient closure theorem.

The step must have an actual canonical polynomial-time machine. The remaining
explicit hypothesis bounds every reachable prefix state's serialization by a
polynomial in the full input encoding. This does not supply that bound for an
arbitrary fold, or assert effective codes for arbitrary TM2 witnesses. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2FoldGenericBounds

open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2PolynomialFold

variable {σ α : Type} [BitstringEncoding σ] [BitstringEncoding α]

/-- A canonical polynomial-time step and a uniform polynomial bound for all
reached prefix states give a canonical polynomial-time fold. The prefix bound
includes the empty and full prefixes and is measured against the complete
encoded `(initial, list)` input. -/
theorem isPolyTime_of_prefix_bound
    (step : ((σ × List Bool) × α) → (σ × List Bool))
    (hstep : ComplexityTheory.IsPolyTime step)
    (hprefix : ∃ p : Polynomial Nat, ∀ (init : σ) (xs pref tail : List α),
      xs = pref ++ tail →
      (BitstringEncoding.bitEncode (fold step (init,[]) pref)).length ≤
        p.eval (BitstringEncoding.bitEncode (init,xs)).length) :
    ComplexityTheory.IsPolyTime (Shared.ComplexityBridge.TM2FoldGenericIO.result step) := by
  obtain ⟨p,hp⟩ := hprefix
  rcases hstep with ⟨m⟩
  let pairSize : Polynomial Nat := Polynomial.C 2 * p + Polynomial.X + Polynomial.C 1
  let q : Polynomial Nat := p + Polynomial.X + pairSize + m.time.comp pairSize
  apply Shared.ComplexityBridge.TM2FoldGenericIO.isPolyTime step m.toTM2ComputableAux q p
  · intro init xs pref item tail hxs
    let state := fold step (init,[]) pref
    let N := (BitstringEncoding.bitEncode (init,xs)).length
    have hs : (BitstringEncoding.bitEncode state).length ≤ p.eval N := hp init xs pref (item::tail) hxs
    have hm : item ∈ xs := by rw [hxs]; simp
    have hi₀ := Shared.ComplexityBridge.TM2MapSizeBounds.element_length_le hm
    have hi : (BitstringEncoding.bitEncode item).length ≤ N := by
      change (BitstringEncoding.bitEncode item).length ≤
        (BitstringEncoding.delimit (BitstringEncoding.bitEncode init) ++ BitstringEncoding.bitEncode xs).length
      simp only [List.length_append]
      omega
    have hpair : (BitstringEncoding.bitEncode (state,item)).length ≤ pairSize.eval N := by
      change (BitstringEncoding.delimit (BitstringEncoding.bitEncode state) ++ BitstringEncoding.bitEncode item).length ≤ _
      simp only [List.length_append,BitstringEncoding.length_delimit,pairSize,
        Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
      omega
    have hxs' : xs = (pref ++ [item]) ++ tail := by simpa [List.append_assoc] using hxs
    have ho := hp init xs (pref ++ [item]) tail hxs'
    rw [fold_append_singleton] at ho
    change (BitstringEncoding.bitEncode (step (state,item))).length ≤ p.eval N at ho
    let e := m.outputsFun (state,item)
    have hn : e.steps ≤ m.time.eval (pairSize.eval N) :=
      le_trans e.steps_le_m (Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono m.time hpair)
    have hr : runSteps m.tm.step e.steps
        (Turing.initList m.tm ((BitstringEncoding.bitEncode (state,item)).map m.inputAlphabet.symm)) =
        some (Turing.haltList m.tm ((BitstringEncoding.bitEncode (step (state,item))).map m.outputAlphabet.symm)) := by
      rw [runSteps_iterate]
      exact e.evals_in_steps
    refine ⟨e.steps,?_,hr,?_,?_,?_,?_⟩ <;>
      simp only [q,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_comp] <;>
      dsimp only [N,state] at * <;> omega
  · intro init xs
    have h := hp init xs xs [] (by simp)
    simpa using h

end Shared.ComplexityBridge.TM2FoldGenericBounds
