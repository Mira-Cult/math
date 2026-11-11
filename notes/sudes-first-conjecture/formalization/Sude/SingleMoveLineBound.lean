import Mathlib.Tactic

/-! A finite line perturbation estimate. It assumes the line support and
value bounds; it does not construct a physical permutation or a square. -/

namespace Sude
noncomputable section

/-- If at most one point of a finite set moves and both its old and new values
lie in `[0,X]`, then the sum changes by at most `X`. The empty and unchanged
cases are included. The map need not be injective for this estimate. -/
theorem single_move_line_sum_bound {α : Type*} [DecidableEq α]
    (T : Finset α) (value : α → ℝ) (σ : α → α) (X : ℝ) (hX : 0 ≤ X)
    (hvalues : ∀ x ∈ T, 0 ≤ value x ∧ value x ≤ X ∧
      0 ≤ value (σ x) ∧ value (σ x) ≤ X)
    (hone : ∀ x ∈ T, ∀ y ∈ T, σ x ≠ x → σ y ≠ y → x = y) :
    |(∑ x ∈ T, value (σ x)) - (∑ x ∈ T, value x)| ≤ X := by
  classical
  rw [← Finset.sum_sub_distrib]
  by_cases hmove : ∃ x ∈ T, σ x ≠ x
  · obtain ⟨z, hz, hzm⟩ := hmove
    have hsum : (∑ x ∈ T, (value (σ x) - value x)) = value (σ z) - value z := by
      apply Finset.sum_eq_single z
      · intro x hx hxz
        have hfix : σ x = x := by
          by_contra hxm
          exact hxz (hone x hx z hz hxm hzm)
        rw [hfix, sub_self]
      · intro hn
        exact (hn hz).elim
    rw [hsum, abs_le]
    obtain ⟨h0, h1, h2, h3⟩ := hvalues z hz
    constructor <;> linarith
  · have hfix : ∀ x ∈ T, σ x = x := by
      intro x hx
      by_contra h
      exact hmove ⟨x, hx, h⟩
    have hsum : (∑ x ∈ T, (value (σ x) - value x)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [hfix x hx, sub_self]
    rw [hsum, abs_zero]
    exact hX

end
end Sude
