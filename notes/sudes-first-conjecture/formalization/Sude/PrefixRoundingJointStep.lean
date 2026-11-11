import Sude.PrefixRoundingBoundaryMove
import Sude.PrefixRoundingJointDirection

/-! A single simultaneous DP2 step, on the supplied fractional coordinates.
This does not yet iterate steps, handle dropped-line errors or construct a
complete allocation. -/
namespace Sude
noncomputable section

/-- The DP2 count and mass hypotheses yield one new active-coordinate vector
inside the unit box. It preserves every occupied group sum and every retained
line equation simultaneously and puts at least one coordinate at a boundary. -/
theorem prefix_joint_rounding_step {S G L : Type*} [DecidableEq G]
    (F : Finset S) (group : S → G) (R : Finset L) (x : S → ℝ)
    (a : L → S → ℝ) (C : ℝ) (hC : 0 ≤ C) (hF : F.Nonempty)
    (hx : ∀ s ∈ F, 0 < x s ∧ x s < 1)
    (hint : ∀ g ∈ F.image group, ∃ z : ℤ,
      (∑ s ∈ F.filter (fun s => group s = g), x s) = z)
    (hnonneg : ∀ l ∈ R, ∀ s ∈ F, 0 ≤ a l s)
    (hrow : ∀ l ∈ R, 10 * C < ∑ s ∈ F, a l s)
    (hcol : ∀ s ∈ F, (∑ l ∈ R, a l s) ≤ 5 * C) :
    ∃ y : {s // s ∈ F} → ℝ,
      (∀ s, 0 ≤ y s ∧ y s ≤ 1) ∧
      (∃ s, y s = 0 ∨ y s = 1) ∧
      (∀ g : {g // g ∈ F.image group},
        (∑ s : {s // s ∈ F}, (if group s.val = g.val then y s else 0)) =
        ∑ s : {s // s ∈ F}, (if group s.val = g.val then x s.val else 0)) ∧
      (∀ l : {l // l ∈ R},
        (∑ s : {s // s ∈ F}, a l.val s.val * y s) =
        ∑ s : {s // s ∈ F}, a l.val s.val * x s.val) := by
  classical
  obtain ⟨d, hd, hgroup, hline⟩ :=
    prefix_joint_rounding_direction F group R x a C hC hF hx hint hnonneg hrow hcol
  have hex : ∃ s : {s // s ∈ F}, d s ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hd
    funext s
    exact hn s
  obtain ⟨t, ht, hbox, hboundary⟩ :=
    prefix_first_boundary_move (fun s : {s // s ∈ F} => x s.val) d
      (fun s => hx s.val s.property) hex
  refine ⟨fun s => x s.val + t * d s, hbox, hboundary, ?_, ?_⟩
  · intro g
    have hk : (∑ s : {s // s ∈ F},
        (if group s.val = g.val then (1 : ℝ) else 0) * d s) = 0 := by
      simpa only [ite_mul, one_mul, zero_mul] using hgroup g
    have heq := prefix_common_step_preserves_equation
      (fun s : {s // s ∈ F} => x s.val) d
      (fun s => if group s.val = g.val then (1 : ℝ) else 0) t hk
    simpa only [ite_mul, one_mul, zero_mul] using heq
  · intro l
    exact prefix_common_step_preserves_equation
      (fun s : {s // s ∈ F} => x s.val) d (fun s => a l.val s.val) t (hline l)

end
end Sude
