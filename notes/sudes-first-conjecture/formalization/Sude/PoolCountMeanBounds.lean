import Sude.PoolPartialSummation

/-! Transfer explicit pointwise odd-prime count bounds to the exact
prescribed-pool mean. The count envelopes and their error budget remain
hypotheses; this module asserts no analytic estimate. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- Every pointwise lower and upper odd-prime-count envelope over the exact
integer range yields two-sided bounds for the actual normalized pool mean.
The denominator is positive for every nonzero order. -/
theorem oddPrimePool_mean_bounds_of_count_envelopes (n : ℕ) (hn : 0 < n)
    (lo hi : ℕ → ℝ)
    (hlo : ∀ k < poolMaximum n, lo k ≤ ((oddPrimePrefix k).card : ℝ))
    (hhi : ∀ k < poolMaximum n, ((oddPrimePrefix k).card : ℝ) ≤ hi k) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    1 - (∑ k ∈ Finset.range (poolMaximum n), hi k) / (N * X) ≤
        ((Lucas.poolTotal n : ℝ) / N) / X ∧
      ((Lucas.poolTotal n : ℝ) / N) / X ≤
        1 - (∑ k ∈ Finset.range (poolMaximum n), lo k) / (N * X) := by
  dsimp only
  let N : ℝ := (n * n : ℕ)
  let X : ℝ := poolMaximum n
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.mul_pos hn hn
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hNX : 0 < N * X := mul_pos hN hX
  have hloSum : (∑ k ∈ Finset.range (poolMaximum n), lo k) ≤
      ∑ k ∈ Finset.range (poolMaximum n), ((oddPrimePrefix k).card : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    exact hlo k (Finset.mem_range.mp hk)
  have hhiSum : (∑ k ∈ Finset.range (poolMaximum n), ((oddPrimePrefix k).card : ℝ)) ≤
      ∑ k ∈ Finset.range (poolMaximum n), hi k := by
    apply Finset.sum_le_sum
    intro k hk
    exact hhi k (Finset.mem_range.mp hk)
  have hid : (Lucas.poolTotal n : ℝ) +
      (∑ k ∈ Finset.range (poolMaximum n), ((oddPrimePrefix k).card : ℝ)) = N * X :=
    oddPrimePool_total_count_identity n
  have hleft : N * X - (∑ k ∈ Finset.range (poolMaximum n), hi k) ≤ Lucas.poolTotal n := by linarith
  have hright : (Lucas.poolTotal n : ℝ) ≤ N * X - (∑ k ∈ Finset.range (poolMaximum n), lo k) := by linarith
  have hdivLeft := div_le_div_of_nonneg_right hleft hNX.le
  have hdivRight := div_le_div_of_nonneg_right hright hNX.le
  have heq (z : ℝ) : (N * X - z) / (N * X) = 1 - z / (N * X) := by
    field_simp
  rw [heq] at hdivLeft hdivRight
  simpa only [div_div] using And.intro hdivLeft hdivRight

/-- A pointwise count approximation and any proved summed absolute-error
budget bound the exact normalized mean error. This allows small-endpoint and
tail errors to be paid separately before supplying `hbudget`. -/
theorem oddPrimePool_mean_error_of_count_approximation (n : ℕ) (hn : 0 < n)
    (approx error : ℕ → ℝ) (E : ℝ)
    (hpoint : ∀ k < poolMaximum n,
      |((oddPrimePrefix k).card : ℝ) - approx k| ≤ error k)
    (hbudget : (∑ k ∈ Finset.range (poolMaximum n), error k) ≤ E) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    |((Lucas.poolTotal n : ℝ) / N) / X -
      (1 - (∑ k ∈ Finset.range (poolMaximum n), approx k) / (N * X))| ≤ E / (N * X) := by
  dsimp only
  let N : ℝ := (n * n : ℕ)
  let X : ℝ := poolMaximum n
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.mul_pos hn hn
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hNX : 0 < N * X := mul_pos hN hX
  have hsum : |∑ k ∈ Finset.range (poolMaximum n),
      (((oddPrimePrefix k).card : ℝ) - approx k)| ≤ E := by
    calc
      _ ≤ ∑ k ∈ Finset.range (poolMaximum n), |((oddPrimePrefix k).card : ℝ) - approx k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (poolMaximum n), error k := by
        apply Finset.sum_le_sum
        intro k hk
        exact hpoint k (Finset.mem_range.mp hk)
      _ ≤ E := hbudget
  rw [Finset.sum_sub_distrib] at hsum
  have hid : (Lucas.poolTotal n : ℝ) +
      (∑ k ∈ Finset.range (poolMaximum n), ((oddPrimePrefix k).card : ℝ)) = N * X :=
    oddPrimePool_total_count_identity n
  have herr : |(Lucas.poolTotal n : ℝ) -
      (N * X - ∑ k ∈ Finset.range (poolMaximum n), approx k)| ≤ E := by
    rw [abs_le] at hsum ⊢
    constructor <;> linarith [hsum.1, hsum.2]
  have heq : ((Lucas.poolTotal n : ℝ) / N) / X -
      (1 - (∑ k ∈ Finset.range (poolMaximum n), approx k) / (N * X)) =
        ((Lucas.poolTotal n : ℝ) - (N * X - ∑ k ∈ Finset.range (poolMaximum n), approx k)) / (N * X) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hNX]
  exact div_le_div_of_nonneg_right herr hNX.le

end
end Sude
