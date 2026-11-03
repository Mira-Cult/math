import Shared.ComplexityBridge.TM2FoldGenericBounds
import Shared.ComplexityBridge.Encodings

/-! A quantitative closure lemma for a unary-clock loop with a fixed
resource, such as a program description. The loop body must already be
canonical polynomial time. Its resource measure is invariant, and its full
serialized state grows by at most a fixed multiple of that measure plus a
fixed constant per step. No computability or cost assertion for an arbitrary
body follows. -/

namespace Shared.ComplexityBridge.TM2FoldFrozenMeasure

open Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2PolynomialFold

variable {σ : Type} [BitstringEncoding σ]

omit [BitstringEncoding σ] in
theorem fold_measure
    (step : ((σ × List Bool) × Bool) → (σ × List Bool))
    (measure : σ → Nat)
    (hinv : ∀ (s : σ × List Bool) b, measure (step (s,b)).1 = measure s.1)
    (s : σ × List Bool) (xs : List Bool) :
    measure (fold step s xs).1 = measure s.1 := by
  induction xs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    change measure (fold step (step (s,b)) bs).1 = measure s.1
    rw [ih, hinv]

theorem fold_growth
    (step : ((σ × List Bool) × Bool) → (σ × List Bool))
    (measure : σ → Nat) (scale overhead : Nat)
    (hinv : ∀ (s : σ × List Bool) b, measure (step (s,b)).1 = measure s.1)
    (hstep : ∀ (s : σ × List Bool) b,
      (BitstringEncoding.bitEncode (step (s,b))).length ≤
        (BitstringEncoding.bitEncode s).length + scale * measure s.1 + overhead)
    (s : σ × List Bool) (xs : List Bool) :
    (BitstringEncoding.bitEncode (fold step s xs)).length ≤
      (BitstringEncoding.bitEncode s).length + xs.length * (scale * measure s.1 + overhead) := by
  induction xs generalizing s with
  | nil => simp [fold]
  | cons b bs ih =>
    change (BitstringEncoding.bitEncode (fold step (step (s,b)) bs)).length ≤
      (BitstringEncoding.bitEncode s).length + (bs.length + 1) * (scale * measure s.1 + overhead)
    have h := ih (step (s,b))
    rw [hinv] at h
    have h' := hstep s b
    simp only [Nat.add_mul, one_mul] at ⊢
    omega

/-- An actual canonical polynomial-time loop body is polynomial time when
iteration follows a unary Boolean-list clock, provided that its invariant
resource measure is bounded by the encoded initial input and each step grows
the encoded state by at most a fixed multiple of that measure plus fixed
overhead. -/
theorem isPolyTime
    (step : ((σ × List Bool) × Bool) → (σ × List Bool))
    (measure : σ → Nat) (scale overhead : Nat)
    (hpoly : ComplexityTheory.IsPolyTime step)
    (hinv : ∀ (s : σ × List Bool) b, measure (step (s,b)).1 = measure s.1)
    (hmeasure : ∀ init, measure init ≤ (BitstringEncoding.bitEncode init).length)
    (hstep : ∀ (s : σ × List Bool) b,
      (BitstringEncoding.bitEncode (step (s,b))).length ≤
        (BitstringEncoding.bitEncode s).length + scale * measure s.1 + overhead) :
    ComplexityTheory.IsPolyTime (TM2FoldGenericIO.result step) := by
  apply TM2FoldGenericBounds.isPolyTime_of_prefix_bound step hpoly
  refine ⟨Polynomial.X + Polynomial.X * (Polynomial.C scale * Polynomial.X + Polynomial.C overhead), ?_⟩
  intro init xs pref tail hxs
  let N := (BitstringEncoding.bitEncode (init,xs)).length
  have hprefix : pref.length ≤ xs.length := by rw [hxs, List.length_append]; omega
  have hN : xs.length ≤ N := by
    dsimp [N]
    change xs.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode init) ++
      BitstringEncoding.bitEncode xs).length
    simp only [List.length_append, bitstring_list_encoded_length]
    omega
  have hinit : (BitstringEncoding.bitEncode (init, ([] : List Bool))).length ≤ N := by
    dsimp [N]
    change (BitstringEncoding.delimit (BitstringEncoding.bitEncode init) ++
      BitstringEncoding.bitEncode ([] : List Bool)).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode init) ++
        BitstringEncoding.bitEncode xs).length
    simp [bitstring_list_encoded_length]
  have hm : measure init ≤ N := by
    have hm₀ := hmeasure init
    dsimp [N]
    change measure init ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode init) ++
      BitstringEncoding.bitEncode xs).length
    simp only [List.length_append, BitstringEncoding.length_delimit]
    omega
  have hg := fold_growth step measure scale overhead hinv hstep (init,[]) pref
  simp only at hg
  have hmul : pref.length * (scale * measure init + overhead) ≤ N * (scale * N + overhead) :=
    Nat.mul_le_mul (le_trans hprefix hN)
      (Nat.add_le_add_right (Nat.mul_le_mul_left scale hm) overhead)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  change (BitstringEncoding.bitEncode (fold step (init,[]) pref)).length ≤ N + N * (scale * N + overhead)
  omega

end Shared.ComplexityBridge.TM2FoldFrozenMeasure
