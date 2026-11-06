import Shared.ComplexityBridge.TM2FoldFrozenMeasure
import Shared.ComplexityBridge.TM2GuardAllStep
import Shared.ComplexityBridge.TM2PairFirst

/-! A canonical polynomial-time unary-clock iteration adapter. The complete
initial state is supplied in the first component; the fold's auxiliary list
starts empty and remains unchanged. No unbounded evaluation is required. -/

namespace Shared.ComplexityBridge.TM2UnaryIterate

open Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2PolynomialFold

variable {σ : Type} [BitstringEncoding σ]

/-- `n` applications of the total data transformation. -/
def run (update : σ → σ) : σ → Nat → σ
  | s, 0 => s
  | s, n + 1 => run update (update s) n

/-- A clock bit advances the transformation once. The Boolean value itself
does not alter the computation. -/
def foldStep (update : σ → σ) (p : ((σ × List Bool) × Bool)) : σ × List Bool :=
  (update p.1.1, p.1.2)

theorem foldStep_isPolyTime (update : σ → σ) (hupdate : ComplexityTheory.IsPolyTime update) :
    ComplexityTheory.IsPolyTime (foldStep update) := by
  let inputState : ((σ × List Bool) × Bool) → σ × List Bool := fun p => p.1
  let first : (σ × List Bool) → σ := fun p => p.1
  let second : (σ × List Bool) → List Bool := fun p => p.2
  have hi : ComplexityTheory.IsPolyTime inputState := TM2PairFirst.first_isPolyTime
  have hf : ComplexityTheory.IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have hfirst := TM2Compose.isPolyTime_comp inputState first hi hf
  have hvalue := TM2Compose.isPolyTime_comp (fun p => first (inputState p)) update hfirst hupdate
  have hsecond := TM2Compose.isPolyTime_comp inputState second hi hs
  change ComplexityTheory.IsPolyTime (fun p : ((σ × List Bool) × Bool) => (update p.1.1,p.1.2))
  simpa [first, second, inputState] using
    (TM2GuardAllStep.pair_isPolyTime (fun p => update (first (inputState p)))
      (fun p => second (inputState p)) hvalue hsecond)

omit [BitstringEncoding σ] in
theorem fold_value (update : σ → σ) (s : σ) (aux : List Bool) (clock : List Bool) :
    fold (foldStep update) (s,aux) clock = (run update s clock.length,aux) := by
  induction clock generalizing s with
  | nil => rfl
  | cons b bs ih =>
    change fold (foldStep update) (update s,aux) bs = (run update s (bs.length+1),aux)
    simpa [run] using ih (update s)

def result (update : σ → σ) (p : σ × List Bool) : σ := run update p.1 p.2.length

omit [BitstringEncoding σ] in
theorem result_eq (update : σ → σ) (p : σ × List Bool) :
    result update p = (TM2FoldGenericIO.result (foldStep update) p).1 := by
  simp [result, TM2FoldGenericIO.result, fold_value]

/-- A direct polynomial bound on every serialized prefix is another way to
establish polynomial-time iteration. The bound includes the empty prefix and
is measured against the entire encoded initial state and unary clock. -/
theorem result_isPolyTime_of_prefix_bound
    (update : σ → σ) (hupdate : ComplexityTheory.IsPolyTime update)
    (hprefix : ∃ p : Polynomial Nat, ∀ (init : σ) (xs pref tail : List Bool),
      xs = pref ++ tail →
      (BitstringEncoding.bitEncode (fold (foldStep update) (init,[]) pref)).length ≤
        p.eval (BitstringEncoding.bitEncode (init,xs)).length) :
    ComplexityTheory.IsPolyTime (result update) := by
  have hfold := TM2FoldGenericBounds.isPolyTime_of_prefix_bound (foldStep update)
    (foldStep_isPolyTime update hupdate) hprefix
  have hfirst : ComplexityTheory.IsPolyTime (TM2PairFirst.first (α := σ) (β := List Bool)) :=
    TM2PairFirst.first_isPolyTime
  have h := TM2Compose.isPolyTime_comp (TM2FoldGenericIO.result (foldStep update))
    (TM2PairFirst.first (α := σ) (β := List Bool)) hfold hfirst
  have he : (fun p : σ × List Bool => TM2PairFirst.first (TM2FoldGenericIO.result (foldStep update) p)) =
      result update := by
    funext p
    exact (result_eq update p).symm
  simpa only [he] using h

/-- An actual polynomial-time update iterates for the supplied unary clock
in polynomial time, under explicit invariant-resource and per-step encoded
growth bounds. These bounds are to be proved for the particular update. -/
theorem result_isPolyTime
    (update : σ → σ) (measure : σ → Nat) (scale overhead : Nat)
    (hupdate : ComplexityTheory.IsPolyTime update)
    (hinv : ∀ s, measure (update s) = measure s)
    (hmeasure : ∀ s, measure s ≤ (BitstringEncoding.bitEncode s).length)
    (hgrowth : ∀ (s : σ) (aux : List Bool),
      (BitstringEncoding.bitEncode (update s,aux)).length ≤
        (BitstringEncoding.bitEncode (s,aux)).length + scale * measure s + overhead) :
    ComplexityTheory.IsPolyTime (result update) := by
  have hfold := TM2FoldFrozenMeasure.isPolyTime (foldStep update) measure scale overhead
    (foldStep_isPolyTime update hupdate)
    (by intro s b; exact hinv s.1) hmeasure
    (by intro s b; exact hgrowth s.1 s.2)
  have hfirst : ComplexityTheory.IsPolyTime (TM2PairFirst.first (α := σ) (β := List Bool)) :=
    TM2PairFirst.first_isPolyTime
  have h := TM2Compose.isPolyTime_comp (TM2FoldGenericIO.result (foldStep update))
    (TM2PairFirst.first (α := σ) (β := List Bool)) hfold hfirst
  have he : (fun p : σ × List Bool => TM2PairFirst.first (TM2FoldGenericIO.result (foldStep update) p)) =
      result update := by
    funext p
    exact (result_eq update p).symm
  simpa only [he] using h

end Shared.ComplexityBridge.TM2UnaryIterate
