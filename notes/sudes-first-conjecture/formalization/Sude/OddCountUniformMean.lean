import Sude.BMORPoolCountMean22

/-!
A coefficient-parametric interface for an aggregate odd-prime count bound,
and its finite pool-mean consequence. No theta-to-count estimate is proved
here; callers must supply the uniform bound. The existing classwise BMOR
hypothesis and its stronger coefficient remain unchanged.
-/
namespace Sude
noncomputable section
open scoped BigOperators

/-- An absolute error bound valid at every real endpoint between 2 and X. -/
def OddPrimeCountUniformBound (X D : ℝ) : Prop :=
  ∀ x, 2 ≤ x → x ≤ X → |oddPrimeCountReal x - liFromTwo x| ≤ D

/-- The existing classwise assumption implies the corresponding aggregate
uniform bound at its existing coefficient. -/
theorem odd_count_uniform_of_bmor_pi_four (h : BMORFinitePiFour) {X : ℝ}
    (hlog : 22 ≤ Real.log X) (hcap : X ≤ (4 * 10 ^ 13 : ℝ)) :
    OddPrimeCountUniformBound X
      ((281649 / 62500 : ℝ) * (Real.sqrt X / Real.log X)) := by
  exact bmor_odd_count_four_uniform_22 h hlog hcap

/-- Any supplied aggregate uniform count error gives a finite Li-sum
approximation for the actual normalized pool mean. D is arbitrary; this
statement does not provide an analytic count estimate. -/
theorem odd_count_uniform_pool_mean_finite_li_sum (n : ℕ) (hn : 0 < n)
    (D : ℝ) (hcount : OddPrimeCountUniformBound (poolMaximum n : ℝ) D) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    |((Lucas.poolTotal n : ℝ) / N) / X -
      (1 - (∑ k ∈ Finset.Ico 2 (poolMaximum n), liFromTwo (k : ℝ)) / (N * X))| ≤
      (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X) := by
  dsimp only
  let X : ℝ := poolMaximum n
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
      have hbound := hcount (k : ℝ) hk2r hkX
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
