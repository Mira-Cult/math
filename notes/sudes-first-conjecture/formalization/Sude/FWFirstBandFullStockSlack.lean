import Sude.FWVaryingStockMass
import Sude.FWAffineFullStockAlgebra

/-! First-band rational slack for the full-stock affine selector. This is
numerical only; it does not assert a selected pair, trace or crossing. -/
namespace Sude
noncomputable section

/-- Normalized conservative stock at global stage j. -/
def fwFirstBandMu (j : ℕ) : ℝ :=
  (403 / 10000 : ℝ) - 2 * (1 / 69780 : ℝ) * j

/-- Through the full 238-stage budget, the available conservative stock
pays a strictly stronger quota than the frozen-eta source requires. -/
theorem fw_first_band_full_stock_quota_slack {j : ℕ} (hj : j ≤ 238) :
    (3347 / 100000 : ℝ) ≤ fwFirstBandMu j ∧
      0 < fwFirstBandMu j ∧
      (6 / 69780 : ℝ) <
        (23 / 48 - 3981035 / 10000000 : ℝ) * (fwFirstBandMu j)^2 := by
  have hjR : (j : ℝ) ≤ 238 := by exact_mod_cast hj
  have hm : (3347 / 100000 : ℝ) ≤ fwFirstBandMu j := by
    unfold fwFirstBandMu
    linarith
  have hp : 0 < fwFirstBandMu j := by linarith
  have hsq : (3347 / 100000 : ℝ)^2 ≤ (fwFirstBandMu j)^2 := by nlinarith
  constructor
  · exact hm
  constructor
  · exact hp
  · nlinarith

/-- The exact absolute stock envelope is its normalized coefficient times X. -/
theorem fw_first_band_mu_mass (X : ℝ) (j : ℕ) :
    fwVaryingStockMass X j = fwFirstBandMu j * X := rfl

/-- For every stage through 238, the uniform full-stock threshold is
strictly larger than the original frozen-eta threshold at the same mass.
No claim about a selected even gap or a trace is made here. -/
theorem fw_first_band_full_stock_threshold_strict {j : ℕ} {X R rho C : ℝ}
    (hj : j ≤ 238) (hX : 0 < X) (hR : 0 < R) (hrho : 0 < rho) :
    fwAffineThreshold 2 rho (3981035 / 10000000) (fwFirstBandMu j * X) R 1 X C <
      fwAffineUniformStockThreshold (fwFirstBandMu j) (6 / 69780) R (23 / 48) rho C := by
  have hslack := fw_first_band_full_stock_quota_slack hj
  have hmu := hslack.2.1
  have hdiv : (6 / 69780 : ℝ) / fwFirstBandMu j <
      (23 / 48 - 3981035 / 10000000 : ℝ) * fwFirstBandMu j := by
    apply (div_lt_iff₀ hmu).2
    nlinarith [hslack.2.2]
  have hcoef : (3981035 / 10000000 : ℝ) * fwFirstBandMu j <
      23 / 48 * fwFirstBandMu j - (6 / 69780 : ℝ) / fwFirstBandMu j := by
    linarith
  have hscaled := mul_lt_mul_of_pos_right hcoef hR
  have hid : (3981035 / 10000000 : ℝ) * (fwFirstBandMu j * X) * R / (1 * X) =
      (3981035 / 10000000 : ℝ) * fwFirstBandMu j * R := by field_simp
  unfold fwAffineThreshold fwAffineUniformStockThreshold
  rw [hid]
  exact mul_lt_mul_of_pos_left (by linarith) (by positivity : 0 < 2 / rho)

/-- At radii at least 11648 and wheel density at most one, the improved
real threshold clears the source threshold by at least three. -/
theorem fw_first_band_full_stock_threshold_add_three {j : ℕ} {X R rho C : ℝ}
    (hj : j ≤ 238) (hX : 0 < X) (hR : 11648 ≤ R)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    fwAffineThreshold 2 rho (3981035 / 10000000) (fwFirstBandMu j * X) R 1 X C + 3 ≤
      fwAffineUniformStockThreshold (fwFirstBandMu j) (6 / 69780) R (23 / 48) rho C := by
  have hm := (fw_first_band_full_stock_quota_slack hj).1
  have hdiv : (6 / 69780 : ℝ) / fwFirstBandMu j ≤ (6 / 69780 : ℝ) / (3347 / 100000) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
  have hcoef : (1 / 7000 : ℝ) ≤
      (23 / 48 - 3981035 / 10000000 : ℝ) * fwFirstBandMu j -
        (6 / 69780 : ℝ) / fwFirstBandMu j := by
    norm_num at hdiv ⊢
    nlinarith
  have hR0 : 0 ≤ R := by linarith
  have hprod := mul_le_mul hcoef hR (by positivity : (0 : ℝ) ≤ 11648)
    (by positivity : 0 ≤ (23 / 48 - 3981035 / 10000000 : ℝ) * fwFirstBandMu j -
      (6 / 69780 : ℝ) / fwFirstBandMu j)
  have hfrac : (2 : ℝ) ≤ 2 / rho := (le_div_iff₀ hrho).2 (by nlinarith)
  have hscale := mul_le_mul hfrac hprod (by positivity : (0 : ℝ) ≤ (1 / 7000) * 11648)
    (by positivity : 0 ≤ 2 / rho)
  have hid : (3981035 / 10000000 : ℝ) * (fwFirstBandMu j * X) * R / (1 * X) =
      (3981035 / 10000000 : ℝ) * fwFirstBandMu j * R := by field_simp
  unfold fwAffineThreshold fwAffineUniformStockThreshold
  rw [hid]
  nlinarith

/-- At the same stage and mass, a gap reaching the full-stock threshold
exceeds the source's rounded-up even increment by at least two. -/
theorem fw_first_band_full_stock_gap_above_source_increment
    {j gap : ℕ} {X R rho C : ℝ}
    (hj : j ≤ 238) (hX : 0 < X) (hR : 11648 ≤ R)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hD : 0 ≤ fwAffineThreshold 2 rho (3981035 / 10000000)
      (fwFirstBandMu j * X) R 1 X C)
    (hgap : fwAffineUniformStockThreshold (fwFirstBandMu j) (6 / 69780) R
      (23 / 48) rho C ≤ (gap : ℝ)) :
    2 * ⌈fwAffineThreshold 2 rho (3981035 / 10000000)
      (fwFirstBandMu j * X) R 1 X C / 2⌉₊ + 2 ≤ gap := by
  let D := fwAffineThreshold 2 rho (3981035 / 10000000) (fwFirstBandMu j * X) R 1 X C
  have hthree := fw_first_band_full_stock_threshold_add_three (C := C) hj hX hR hrho hrho1
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ D / 2 by positivity)
  have hreal : (((2 * ⌈D / 2⌉₊ + 1 : ℕ) : ℝ)) < gap := by
    push_cast
    dsimp [D] at *
    linarith
  have hnat : 2 * ⌈D / 2⌉₊ + 1 < gap := by exact_mod_cast hreal
  exact Nat.succ_le_iff.mpr hnat

end
end Sude
