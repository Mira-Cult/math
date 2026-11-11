import Sude.BMORPoolScalarMean

/-! Retain the shared `Li(X)` term when converting the exact pool count
and the integrated count into a normalized mean. No numerical target mean
or new analytic assumption is asserted. -/
namespace Sude
noncomputable section

/-- Correlating the endpoint count with the partial-summation identity
cancels the main `Li(X)` term before applying BG's Li estimates. Both
BMOR count errors, the Li(4) endpoint, and the discretization allowance
are retained explicitly. -/
theorem bmor_pool_mean_correlated_bounds (h : BMORFinitePiFour) (n : ℕ)
    (hn : 0 < n) (hlog : 22 ≤ Real.log (poolMaximum n : ℝ))
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ)) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    let u : ℝ := Real.log X
    let q : ℝ := N / X
    let D : ℝ := (281649 / 62500 : ℝ) * (Real.sqrt X / u)
    let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
    bgLiLowerNorm (2*u) / q - D/N - liFromTwo 4/(N*X) - E ≤
      ((Lucas.poolTotal n : ℝ) / N) / X ∧
    ((Lucas.poolTotal n : ℝ) / N) / X ≤
      bgLiUpperNorm (2*u) / q + D/N - liFromTwo 4/(N*X) + E +
        bgLiUpperNorm u/N := by
  dsimp only
  let N : ℝ := (n * n : ℕ)
  let X : ℝ := poolMaximum n
  let u : ℝ := Real.log X
  let q : ℝ := N / X
  let D : ℝ := (281649 / 62500 : ℝ) * (Real.sqrt X / u)
  let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.mul_pos hn hn
  have hX2 : (2 : ℝ) ≤ X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).two_le
  have hX : 0 < X := by linarith
  have hq : 0 < q := div_pos hN hX
  have hli := bg_li_normalized_and_square hX2 hlog
  dsimp only at hli
  have hlo := div_le_div_of_nonneg_right hli.2.2.1.le hq.le
  have hhi := div_le_div_of_nonneg_right hli.2.2.2.le hq.le
  have hquot : (liFromTwo (X^2) / X^2) / q = liFromTwo (X^2) / (N*X) := by
    dsimp [q]
    field_simp
  rw [hquot] at hlo hhi
  have hend := div_le_div_of_nonneg_right hli.2.1.le hN.le
  have hend_eq : (liFromTwo X / X) / N = liFromTwo X / (N*X) := by field_simp
  rw [hend_eq] at hend
  have hpoint := abs_le.mp (bmor_poolMaximum_count_error h n hcap)
  have hp1 := div_le_div_of_nonneg_right hpoint.1 hN.le
  have hp2 := div_le_div_of_nonneg_right hpoint.2 hN.le
  simp only [sub_div, neg_div] at hp1 hp2
  have hm := bmor_pool_mean_continuous_bounds h n hn hlog hcap
  dsimp only at hm
  have hidentity : 1 - (X * liFromTwo X - liFromTwo (X^2) + liFromTwo 4) / (N*X) =
      liFromTwo (X^2)/(N*X) + (N - liFromTwo X)/N - liFromTwo 4/(N*X) := by
    field_simp
    ring
  dsimp [N, X, u, q, D, E] at *
  rw [hidentity] at hm
  simp only [sub_div] at hm
  constructor <;> linarith [hm.1, hm.2, hlo, hhi, hend, hp1, hp2]

end
end Sude
