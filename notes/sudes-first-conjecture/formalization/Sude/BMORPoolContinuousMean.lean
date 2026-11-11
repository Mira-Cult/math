import Sude.BMORPoolCountMean22
import Sude.LiSumEnclosure

/-! The finite q=4 mean estimate and the proved Li sum enclosure yield a
continuous expression. No numerical estimate for Li is imported here. -/

namespace Sude
noncomputable section
open scoped BigOperators

/-- Conditional continuous-expression bounds for the normalized pool mean.
The lower-side error is the BMOR contribution alone; the upper-side error
also pays the endpoint `Li(X)` for replacing the finite sum by an integral.
The term `Li(4)` records the lower endpoint in the exact integral identity. -/
theorem bmor_pool_mean_continuous_bounds (h : BMORFinitePiFour) (n : ℕ)
    (hn : 0 < n)
    (hlog : 22 ≤ Real.log (poolMaximum n : ℝ))
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ)) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    let D : ℝ := (281649 / 62500 : ℝ) * (Real.sqrt X / Real.log X)
    let A : ℝ := X * liFromTwo X - liFromTwo (X ^ 2) + liFromTwo 4
    let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
    (-E) ≤ ((Lucas.poolTotal n : ℝ) / N) / X - (1 - A / (N * X)) ∧
      ((Lucas.poolTotal n : ℝ) / N) / X - (1 - A / (N * X)) ≤
        E + liFromTwo X / (N * X) := by
  dsimp only
  let N : ℝ := (n * n : ℕ)
  let X : ℝ := poolMaximum n
  let D : ℝ := (281649 / 62500 : ℝ) * (Real.sqrt X / Real.log X)
  let A : ℝ := X * liFromTwo X - liFromTwo (X ^ 2) + liFromTwo 4
  let S : ℝ := ∑ k ∈ Finset.Ico 2 (poolMaximum n), liFromTwo (k : ℝ)
  let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.mul_pos hn hn
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hNX : 0 < N * X := mul_pos hN hX
  have hsum : S ≤ A ∧ A ≤ S + liFromTwo X := by
    exact liFromTwo_nat_sum_identity_enclosure (poolMaximum_prime n).two_le
  have hlow : S / (N * X) ≤ A / (N * X) :=
    div_le_div_of_nonneg_right hsum.1 hNX.le
  have hhigh : A / (N * X) ≤ S / (N * X) + liFromTwo X / (N * X) := by
    have ht := div_le_div_of_nonneg_right hsum.2 hNX.le
    simpa only [add_div] using ht
  have hfinite : |((Lucas.poolTotal n : ℝ) / N) / X - (1 - S / (N * X))| ≤ E := by
    exact bmor_pool_mean_finite_li_sum_22 h n hn hlog hcap
  have hfinite' := abs_le.mp hfinite
  constructor <;> linarith [hfinite'.1, hfinite'.2]

end
end Sude
