import Sude.FWBT16EntryGate
import Sude.FWFirstBandFullStockSlack

/-! Numerical BT16 width and sixfold pair-budget gates. The actual stock,
prime-pair population, and Montgomery--Vaughan hypothesis remain separate. -/
namespace Sude
noncomputable section

/-- The first-band full-stock envelope pays the BT16 width and source
pair-budget inequalities for a `6Q` candidate matching. No BT stage or
stock availability is asserted. -/
theorem fw_bt16_first_band_width_and_budget {j Q R : ℕ} {X : ℝ}
    (hj : j ≤ 238) (hX : 0 < X)
    (hQ : (Q : ℝ) ≤ (1 / 69780 : ℝ) * X)
    (hR : 171331843 ≤ R) :
    let m := fwFirstBandMu j
    let D := 8 * ((3981035 / 10000000 : ℝ) * m * R - 1 / 2)
    2 < D ∧ D ≤ R ∧ Real.exp 16 ≤ D / 2 ∧
      2 * ((6 * Q : ℕ) : ℝ) * X ≤
        (1 / (2 * (1 + 1 / 23)) - 3981035 / 10000000 : ℝ) * (m * X)^2 * 2 := by
  dsimp only
  have hm := fw_first_band_full_stock_quota_slack hj
  have hmupper : fwFirstBandMu j ≤ (403 / 10000 : ℝ) := by
    unfold fwFirstBandMu
    have hjnonneg : (0 : ℝ) ≤ j := by positivity
    linarith
  have hgate := fw_bt16_fixed_mass_capped_gate (m := fwFirstBandMu j) (R := R)
    (by linarith [hm.1]) hR
  dsimp only at hgate
  have hDexp : Real.exp 16 ≤
      (8 * ((3981035 / 10000000 : ℝ) * fwFirstBandMu j * R - 1 / 2)) / 2 :=
    hgate.1.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hR0 : (0 : ℝ) ≤ R := by positivity
  have hmul := mul_le_mul_of_nonneg_right hmupper hR0
  have hDle : 8 * ((3981035 / 10000000 : ℝ) * fwFirstBandMu j * R - 1 / 2) ≤ R := by
    nlinarith
  have hQX := mul_le_mul_of_nonneg_right hQ hX.le
  have hbudget := mul_le_mul_of_nonneg_right hm.2.2.le (sq_nonneg X)
  have hnum : (1 / (2 * (1 + 1 / 23)) - 3981035 / 10000000 : ℝ) =
      23 / 48 - 3981035 / 10000000 := by norm_num
  refine ⟨hgate.2, hDle, hDexp, ?_⟩
  rw [hnum]
  push_cast
  nlinarith

end
end Sude
