import Sude.PrefixRoundingEquationCount
import Sude.DPRoundingKernel

/-! One nonzero simultaneous direction for all active groups and retained
lines. Step size, termination and discrepancy are separate obligations. -/
namespace Sude
noncomputable section

/-- Under the DP2 integrality and fixed-coefficient mass hypotheses, there is
a nonzero direction on the fractional coordinates preserving every active
group sum and every retained line equation simultaneously. -/
theorem prefix_joint_rounding_direction {S G L : Type*} [DecidableEq G]
    (F : Finset S) (group : S → G) (R : Finset L) (x : S → ℝ)
    (a : L → S → ℝ) (C : ℝ) (hC : 0 ≤ C) (hF : F.Nonempty)
    (hx : ∀ s ∈ F, 0 < x s ∧ x s < 1)
    (hint : ∀ g ∈ F.image group, ∃ z : ℤ,
      (∑ s ∈ F.filter (fun s => group s = g), x s) = z)
    (hnonneg : ∀ l ∈ R, ∀ s ∈ F, 0 ≤ a l s)
    (hrow : ∀ l ∈ R, 10 * C < ∑ s ∈ F, a l s)
    (hcol : ∀ s ∈ F, (∑ l ∈ R, a l s) ≤ 5 * C) :
    ∃ d : {s // s ∈ F} → ℝ, d ≠ 0 ∧
      (∀ g : {g // g ∈ F.image group},
        ∑ s : {s // s ∈ F}, (if group s.val = g.val then d s else 0) = 0) ∧
      (∀ l : {l // l ∈ R}, ∑ s : {s // s ∈ F}, a l.val s.val * d s = 0) := by
  classical
  let V := {s // s ∈ F}
  let E := {g // g ∈ F.image group} ⊕ {l // l ∈ R}
  let A : Matrix E V ℝ := fun e s => match e with
    | Sum.inl g => if group s.val = g.val then 1 else 0
    | Sum.inr l => a l.val s.val
  have hcount : Fintype.card E < Fintype.card V := by
    simpa [E, V] using
      prefix_rounding_integral_equations_count F group R x a C hC hF hx hint hnonneg hrow hcol
  obtain ⟨d, hd, heq⟩ := dp_underdetermined_direction A hcount
  refine ⟨d, hd, ?_, ?_⟩
  · intro g
    simpa only [A, ite_mul, one_mul, zero_mul] using heq (Sum.inl g)
  · intro l
    simpa only [A] using heq (Sum.inr l)

end
end Sude
