import Sude.FWAffineWheelPairSupply

/-! Algebra for an affine candidate threshold using the actual surviving stock.
This is a conditional counting interface; it asserts neither prime supply nor
an admissible threshold or trace. -/
namespace Sude
noncomputable section

/-- Threshold obtained by spending all binned-pair surplus above the
existing `Z`-matching budget, using the actual stock count `N`. -/
def fwAffineFullStockThreshold (N R X c0 rho C Z : ℝ) : ℝ :=
  (2 / rho) * (c0 * N * R / X - 1 / 2 - C - Z * R / N)

/-- With the source quota, the full-stock threshold weakly dominates the
original AW threshold. All stock and quota premises remain explicit. -/
theorem fw_affine_full_stock_threshold_ge_source
    {N M Mf R X c0 rho C Z eta : ℝ}
    (hR : 0 ≤ R) (hX : 0 < X) (hrho : 0 < rho)
    (heta : 0 ≤ eta) (heps : eta ≤ c0) (hMf : 0 < Mf)
    (hM : Mf ≤ M) (hN : M ≤ N)
    (hquota : Z * X ≤ (c0 - eta) * Mf ^ 2) :
    fwAffineThreshold 2 rho eta M R 1 X C ≤
      fwAffineFullStockThreshold N R X c0 rho C Z := by
  have hMpos : 0 < M := lt_of_lt_of_le hMf hM
  have hNpos : 0 < N := lt_of_lt_of_le hMpos hN
  have hsq : Mf ^ 2 ≤ N ^ 2 := by nlinarith
  have heps0 : 0 ≤ c0 - eta := by linarith
  have hepssq := mul_le_mul_of_nonneg_left hsq heps0
  have hdiff : 0 ≤ eta * N * (N - M) := by positivity
  have hbudget : Z * X ≤ c0 * N ^ 2 - eta * M * N := by nlinarith
  have hfac : 0 ≤ R / (N * X) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hbudget hfac
  have hidleft : (Z * X) * (R / (N * X)) = Z * R / N := by
    field_simp
  have hidright : (c0 * N ^ 2 - eta * M * N) * (R / (N * X)) =
      c0 * N * R / X - eta * M * R / X := by
    field_simp
  rw [hidleft, hidright] at hscaled
  unfold fwAffineThreshold fwAffineFullStockThreshold
  have hmul := mul_le_mul_of_nonneg_left (show eta * M * R / X - (1 / 2 + C) ≤
      c0 * N * R / X - 1 / 2 - C - Z * R / N by linarith) (by positivity : 0 ≤ 2 / rho)
  simpa using hmul

/-- The short-pair allowance at the full-stock threshold cancels exactly,
leaving the `Z*R` pair budget; no strictness or integer rounding is hidden. -/
theorem fw_affine_full_stock_threshold_cancel
    {N R X c0 rho C Z : ℝ} (hN : N ≠ 0) (hX : X ≠ 0) (hrho : rho ≠ 0) :
    N * (rho * fwAffineFullStockThreshold N R X c0 rho C Z / 2 + C) =
      c0 * N ^ 2 * R / X - N / 2 - Z * R := by
  unfold fwAffineFullStockThreshold
  field_simp
  ring

/-- A computable stock-and-quota envelope for the full-stock threshold. -/
def fwAffineUniformStockThreshold (mu b R c0 rho C : ℝ) : ℝ :=
  (2 / rho) * ((c0 * mu - b / mu) * R - (1 / 2 + C))

/-- Lower-bounding actual stock by `mu*X` and upper-bounding the matching
quota by `b*X` yields a uniform lower bound for the full-stock threshold. -/
theorem fw_affine_uniform_stock_threshold_le_full
    {N R X c0 rho C Z mu b : ℝ}
    (hmu : 0 < mu) (hb : 0 ≤ b) (hR : 0 ≤ R) (hX : 0 < X)
    (hc0 : 0 ≤ c0) (hrho : 0 < rho)
    (hstock : mu * X ≤ N) (hquota : Z ≤ b * X) :
    fwAffineUniformStockThreshold mu b R c0 rho C ≤
      fwAffineFullStockThreshold N R X c0 rho C Z := by
  have hNpos : 0 < N := lt_of_lt_of_le (mul_pos hmu hX) hstock
  have hNdiv : mu ≤ N / X := (le_div_iff₀ hX).2 hstock
  have hZmu := mul_le_mul_of_nonneg_left hquota hmu.le
  have hbN := mul_le_mul_of_nonneg_left hstock hb
  have hZdiv : Z / N ≤ b / mu := by
    apply (div_le_div_iff₀ hNpos hmu).2
    nlinarith
  have hc := mul_le_mul_of_nonneg_left hNdiv hc0
  have hcoef : c0 * mu - b / mu ≤ c0 * (N / X) - Z / N := by linarith
  have hscale := mul_le_mul_of_nonneg_right hcoef hR
  unfold fwAffineUniformStockThreshold fwAffineFullStockThreshold
  have hbound : (c0 * mu - b / mu) * R - (1 / 2 + C) ≤
      c0 * N * R / X - 1 / 2 - C - Z * R / N := by
    ring_nf at hscale ⊢
    linarith
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- Under a source-style quota and `M≤mu*X`, the uniform threshold
dominates the original source threshold. -/
theorem fw_affine_uniform_stock_threshold_ge_source
    {M R X c0 rho C mu b eta : ℝ}
    (hmu : 0 < mu) (hR : 0 ≤ R) (hX : 0 < X) (hrho : 0 < rho)
    (heta : 0 ≤ eta) (hM : M ≤ mu * X)
    (hquota : b ≤ (c0 - eta) * mu ^ 2) :
    fwAffineThreshold 2 rho eta M R 1 X C ≤
      fwAffineUniformStockThreshold mu b R c0 rho C := by
  have hMX : M / X ≤ mu := (div_le_iff₀ hX).2 hM
  have hetaM := mul_le_mul_of_nonneg_left hMX heta
  have hbdiv : b / mu ≤ (c0 - eta) * mu := by
    apply (div_le_iff₀ hmu).2
    nlinarith [hquota]
  have hcoef : eta * (M / X) ≤ c0 * mu - b / mu := by linarith
  have hscale := mul_le_mul_of_nonneg_right hcoef hR
  unfold fwAffineThreshold fwAffineUniformStockThreshold
  have hbound : eta * M * R / (1 * X) - (1 / 2 + C) ≤
      (c0 * mu - b / mu) * R - (1 / 2 + C) := by
    ring_nf at hscale ⊢
    linarith
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end
end Sude
