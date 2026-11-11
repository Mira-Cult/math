import Sude.PermutationStageMGF
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! A finite product moment for independently chosen fair binary outcomes.
The one-coordinate moment bounds are supplied; no permutation, line, or
concentration conclusion is asserted. -/
namespace Sude
noncomputable section

/-- The uniform average exponential moment of a sum of binary-coordinate
scores is at most the product of supplied one-coordinate moment bounds. -/
theorem finite_independent_binary_exp_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (score : ι → Bool → ℝ) (bound : ι → ℝ) (t : ℝ)
    (hbound : ∀ i, (Real.exp (t * score i false) + Real.exp (t * score i true)) / 2 ≤ bound i) :
    (∑ ω : ι → Bool, Real.exp (t * ∑ i, score i (ω i))) /
      (2 : ℝ) ^ Fintype.card ι ≤ ∏ i, bound i := by
  classical
  have hfactor : (∑ ω : ι → Bool, Real.exp (t * ∑ i, score i (ω i))) =
      ∏ i, (Real.exp (t * score i false) + Real.exp (t * score i true)) := by
    calc
      _ = ∑ ω : ι → Bool, ∏ i, Real.exp (t * score i (ω i)) := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum]
      _ = ∏ i, ∑ b : Bool, Real.exp (t * score i b) := by
        symm
        exact Fintype.prod_sum _
      _ = _ := by simp only [Fintype.sum_bool, add_comm]
  rw [hfactor]
  have hdiv : (∏ i, (Real.exp (t * score i false) + Real.exp (t * score i true))) /
      (2 : ℝ) ^ Fintype.card ι =
      ∏ i, ((Real.exp (t * score i false) + Real.exp (t * score i true)) / 2) := by
    rw [Finset.prod_div_distrib]
    simp
  rw [hdiv]
  apply Finset.prod_le_prod
  · intro i _
    positivity
  · intro i _
    exact hbound i

/-- A uniform coordinate-wise bound also holds after averaging over an
arbitrary finite outer choice. The binary scores may depend on that choice;
no independence between the outer score and the binary score is assumed. -/
theorem finite_outer_binary_exp_moment {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (outer : α → ℝ)
    (score : α → ι → Bool → ℝ) (bound : ι → ℝ) (t : ℝ)
    (hbound : ∀ a i, (Real.exp (t * score a i false) + Real.exp (t * score a i true)) / 2 ≤ bound i) :
    (∑ a, ∑ ω : ι → Bool, Real.exp (t * (outer a + ∑ i, score a i (ω i)))) /
      ((Fintype.card α : ℝ) * (2 : ℝ) ^ Fintype.card ι) ≤
      ((∑ a, Real.exp (t * outer a)) / (Fintype.card α : ℝ)) * ∏ i, bound i := by
  classical
  have hinner (a : α) :
      (∑ ω : ι → Bool, Real.exp (t * (outer a + ∑ i, score a i (ω i)))) /
        (2 : ℝ) ^ Fintype.card ι ≤ Real.exp (t * outer a) * ∏ i, bound i := by
    have h := finite_independent_binary_exp_moment (score a) bound t (hbound a)
    have heq : (∑ ω : ι → Bool, Real.exp (t * (outer a + ∑ i, score a i (ω i)))) =
        Real.exp (t * outer a) * ∑ ω : ι → Bool, Real.exp (t * ∑ i, score a i (ω i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      rw [mul_add, Real.exp_add]
    rw [heq, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h (le_of_lt (Real.exp_pos _))
  have hcard : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  calc
    _ = (∑ a, (∑ ω : ι → Bool,
        Real.exp (t * (outer a + ∑ i, score a i (ω i)))) /
          (2 : ℝ) ^ Fintype.card ι) / (Fintype.card α : ℝ) := by
      rw [← Finset.sum_div, div_div]
      congr 1
      ring
    _ ≤ (∑ a, Real.exp (t * outer a) * ∏ i, bound i) / (Fintype.card α : ℝ) := by
      apply div_le_div_of_nonneg_right _ hcard
      exact Finset.sum_le_sum (fun a _ => hinner a)
    _ = _ := by rw [← Finset.sum_mul]; ring

end
end Sude
