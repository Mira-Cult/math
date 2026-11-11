import Sude.FWReservedMidpointComponentAssembly

/-! Algebra for a supplied line midpoint invoice, local rectangle/spare
estimate, and full-reservation scalar cancellation. The free residual remains
explicit; no geometry, free-cell estimate, numeric gate, or flow is asserted. -/
namespace Sude
noncomputable section

/-- The global spare deviation is used only through the supplied cancellation
bound. `local` is the distinct per-line centered rectangle/spare contribution. -/
theorem reserved_midpoint_cancellation_arithmetic
    (R W S F w t k n μ ν A E L C : ℝ)
    (hcore : |R - (W + S + F)| ≤ E)
    (hlocal : |(W - w * μ) - 12 * A + (S - t * μ)| ≤ L)
    (hcancel : |12 * A + k * (ν - μ)| ≤ C)
    (hincidence : w + t + k = n) :
    |R - (n * μ + (F - k * ν))| ≤ E + L + C := by
  have heq : R - (n * μ + (F - k * ν)) =
      (R - (W + S + F)) + ((W - w * μ) - 12 * A + (S - t * μ)) +
        (12 * A + k * (ν - μ)) := by
    rw [← hincidence]
    ring
  rw [heq]
  have h₁ := abs_add_le (R - (W + S + F)) ((W - w * μ) - 12 * A + (S - t * μ))
  have h₂ := abs_add_le ((R - (W + S + F)) + ((W - w * μ) - 12 * A + (S - t * μ)))
    (12 * A + k * (ν - μ))
  linarith

/-- Finite line form: all stage weights, spare cells, free cells and the free
residual are displayed. The incidence equality is an explicit hypothesis. -/
theorem finite_reserved_midpoint_cancellation {I J α : Type*}
    [Fintype I] [Fintype J] [DecidableEq α]
    (weight : I → J → ℝ) (means : I → ℝ) (value : α → ℝ)
    (spare free : Finset α) (R n μ ν A E L C : ℝ)
    (hcore : |R - ((∑ j, ∑ i, weight j i * means j) +
      (∑ z ∈ spare, value z) + (∑ z ∈ free, value z))| ≤ E)
    (hlocal : |(∑ j, ∑ i, weight j i * (means j - μ)) - 12 * A +
      (∑ z ∈ spare, (value z - μ))| ≤ L)
    (hcancel : |12 * A + (free.card : ℝ) * (ν - μ)| ≤ C)
    (hincidence : (∑ j, ∑ i, weight j i) + (spare.card : ℝ) + (free.card : ℝ) = n) :
    |R - (n * μ + ∑ z ∈ free, (value z - ν))| ≤ E + L + C := by
  classical
  have hweight : (∑ j, ∑ i, weight j i * (means j - μ)) =
      (∑ j, ∑ i, weight j i * means j) - (∑ j, ∑ i, weight j i) * μ := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  have hspare : (∑ z ∈ spare, (value z - μ)) =
      (∑ z ∈ spare, value z) - (spare.card : ℝ) * μ := by
    simp [Finset.sum_sub_distrib, nsmul_eq_mul]
  have hfree : (∑ z ∈ free, (value z - ν)) =
      (∑ z ∈ free, value z) - (free.card : ℝ) * ν := by
    simp [Finset.sum_sub_distrib, nsmul_eq_mul]
  rw [hweight, hspare] at hlocal
  rw [hfree]
  exact reserved_midpoint_cancellation_arithmetic R
    (∑ j, ∑ i, weight j i * means j) (∑ z ∈ spare, value z) (∑ z ∈ free, value z)
    (∑ j, ∑ i, weight j i) spare.card free.card n μ ν A E L C
    hcore hlocal hcancel hincidence

end
end Sude
