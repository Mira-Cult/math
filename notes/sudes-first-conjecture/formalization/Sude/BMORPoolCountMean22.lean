import Sude.BMORPoolCountMean
import Sude.UniformSqrtLog22

/-! Extend the conditional q=4 error and finite-sum pool-mean bounds to
`log X ≥ 22`. No additional analytic input is introduced. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- The q=4 odd-prime-count error is uniform through X once log X ≥ 22. -/
theorem bmor_odd_count_four_uniform_22 (h : BMORFinitePiFour) {X : ℝ}
    (hlog : 22 ≤ Real.log X) (hcap : X ≤ (4 * 10 ^ 13 : ℝ)) :
    ∀ x, 2 ≤ x → x ≤ X →
      |oddPrimeCountReal x - liFromTwo x| ≤
        (281649 / 62500 : ℝ) * (Real.sqrt X / Real.log X) := by
  apply uniform_sqrt_log_error_22 (by norm_num) hlog
  intro x hx hxX
  exact bmor_odd_count_four_pointwise h hx (le_trans hxX hcap)

/-- Under the explicit BMOR q=4 pointwise computation, the actual normalized
pool mean is approximated by the finite sum of `Li(k)` for 2 ≤ k < X.
The counts at 0 and 1 are both exactly zero and are paid with zero error;
no meaning is assigned here to the source integral below 2. -/
theorem bmor_pool_mean_finite_li_sum_22 (h : BMORFinitePiFour) (n : ℕ)
    (hn : 0 < n)
    (hlog : 22 ≤ Real.log (poolMaximum n : ℝ))
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ)) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    let D : ℝ := (281649 / 62500 : ℝ) * (Real.sqrt X / Real.log X)
    |((Lucas.poolTotal n : ℝ) / N) / X -
      (1 - (∑ k ∈ Finset.Ico 2 (poolMaximum n), liFromTwo (k : ℝ)) / (N * X))| ≤
      (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X) := by
  dsimp only
  let X : ℝ := poolMaximum n
  let D : ℝ := (281649 / 62500 : ℝ) * (Real.sqrt X / Real.log X)
  let approx : ℕ → ℝ := fun k => if 2 ≤ k then liFromTwo (k : ℝ) else 0
  let err : ℕ → ℝ := fun k => if 2 ≤ k then D else 0
  have hpref0 : oddPrimePrefix 0 = ∅ := by decide
  have hpref1 : oddPrimePrefix 1 = ∅ := by decide
  have hpoint : ∀ k < poolMaximum n,
      |((oddPrimePrefix k).card : ℝ) - approx k| ≤ err k := by
    intro k hk
    by_cases hk2 : 2 ≤ k
    · have hkX : (k : ℝ) ≤ X := by
        dsimp [X]
        exact_mod_cast (le_of_lt hk)
      have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      have hbound := bmor_odd_count_four_uniform_22 h hlog hcap (k : ℝ) hk2r hkX
      simp only [oddPrimeCountReal_natCast] at hbound
      simpa [approx, err, hk2] using hbound
    · have hsmall : k = 0 ∨ k = 1 := by omega
      rcases hsmall with rfl | rfl
      · simp [approx, err, hpref0]
      · simp [approx, err, hpref1]
  have hfilter : (Finset.range (poolMaximum n)).filter (fun k => 2 ≤ k) =
      Finset.Ico 2 (poolMaximum n) := by
    ext k
    simp [and_comm]
  have hsumapprox : (∑ k ∈ Finset.range (poolMaximum n), approx k) =
      ∑ k ∈ Finset.Ico 2 (poolMaximum n), liFromTwo (k : ℝ) := by
    dsimp [approx]
    rw [← Finset.sum_filter, hfilter]
  have hsumerr : (∑ k ∈ Finset.range (poolMaximum n), err k) =
      (((poolMaximum n - 2 : ℕ) : ℝ) * D) := by
    dsimp [err]
    rw [← Finset.sum_filter, hfilter]
    simp [Nat.card_Ico, nsmul_eq_mul]
  have hb := oddPrimePool_mean_error_of_count_approximation n hn approx err
    (((poolMaximum n - 2 : ℕ) : ℝ) * D) hpoint (le_of_eq hsumerr)
  dsimp only at hb
  rw [hsumapprox] at hb
  exact hb

end
end Sude
