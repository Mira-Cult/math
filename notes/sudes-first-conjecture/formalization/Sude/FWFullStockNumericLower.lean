import Sude.FWFullStockIteration

/-! Computable lower increments for the first-band full-stock threshold. The
lower envelope uses the global bound mu_j ≥ 3347/100000, not a claim that
crossing or any phase occurs. -/
namespace Sude
noncomputable section

def fwEnhancedRhoNum (i : Fin 8) : ℕ := ![6144,110592,221184,884736,26542080,955514880,38220595200,1605264998400] i
def fwEnhancedRhoDen (i : Fin 8) : ℕ := ![17017,323323,676039,2800733,86822723,3212440751,131710070791,5663533044013] i
def fwEnhancedErrNum (i : Fin 8) : ℕ := ![13820,476024,18199504,839610208,150976832,3025505777792,7722793179392,1412903474340352] i
def fwEnhancedErrDen (i : Fin 8) : ℕ := ![1001,17017,323323,7436429,667667,6685349671,8529584063,780128880839] i

theorem fw_enhanced_wheel_rationals (i : Fin 8) :
    0 < fwEnhancedRhoNum i ∧ 0 < fwEnhancedRhoDen i ∧ 0 < fwEnhancedErrDen i ∧
    fwMixedWheelRho i = (fwEnhancedRhoNum i : ℝ) / fwEnhancedRhoDen i ∧
    fwMixedWheelError i = (fwEnhancedErrNum i : ℝ) / fwEnhancedErrDen i := by
  fin_cases i <;> norm_num [fwEnhancedRhoNum, fwEnhancedRhoDen, fwEnhancedErrNum,
    fwEnhancedErrDen, fwMixedWheelRho, fwMixedWheelError]

/-- A linear numerator for a lower envelope of the full-stock rate. -/
def fwEnhancedLowerRate (j : ℕ) : ℕ := 93840443727 - 76981000 * j

theorem fw_enhanced_lower_rate (j : ℕ) (hj : j ≤ 238) :
    ((fwEnhancedLowerRate j : ℕ) : ℝ) / 5605287840000 ≤
      (23 / 48 : ℝ) * fwFirstBandMu j - (6 / 69780 : ℝ) / fwFirstBandMu j := by
  have hm := (fw_first_band_full_stock_quota_slack hj).1
  have hdiv : (6 / 69780 : ℝ) / fwFirstBandMu j ≤ (6 / 69780 : ℝ) / (3347 / 100000) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
  have hjsub : 76981000 * j ≤ 93840443727 := by omega
  unfold fwEnhancedLowerRate
  rw [Nat.cast_sub hjsub]
  unfold fwFirstBandMu
  unfold fwFirstBandMu at hdiv
  push_cast
  norm_num at hdiv ⊢
  linarith

/-- Integer floor of a rational lower bound on half the enhanced threshold.
Natural subtraction is safe even if the lower bound is negative. -/
def fwEnhancedLowerCount (i : Fin 8) (j R : ℕ) : ℕ :=
  fwEnhancedRhoDen i *
    (2 * fwEnhancedErrDen i * fwEnhancedLowerRate j * R -
      5605287840000 * (fwEnhancedErrDen i + 2 * fwEnhancedErrNum i)) /
    (2 * 5605287840000 * fwEnhancedErrDen i * fwEnhancedRhoNum i)

/-- The integer count is monotone in the radius, including through zero. -/
theorem fw_enhanced_lower_count_mono (i : Fin 8) (j : ℕ) :
    Monotone (fwEnhancedLowerCount i j) := by
  intro a b hab
  unfold fwEnhancedLowerCount
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_left
  apply Nat.sub_le_sub_right
  exact Nat.mul_le_mul_left _ hab

/-- The executable lower count is bounded by the enhanced threshold rounded
down to an integer; negative rational inputs are handled by natural truncation. -/
theorem fw_enhanced_lower_count_le (i : Fin 8) (j R : ℕ) (hj : j ≤ 238) :
    fwEnhancedLowerCount i j R ≤ ⌊fwFullStockEnhancedD i j R / 2⌋₊ := by
  let p := fwEnhancedRhoNum i
  let q := fwEnhancedRhoDen i
  let c := fwEnhancedErrNum i
  let e := fwEnhancedErrDen i
  let a := fwEnhancedLowerRate j
  let P := 2 * e * a * R
  let N := 5605287840000 * (e + 2 * c)
  let den := 2 * 5605287840000 * e * p
  obtain ⟨hp, hq, he, hrho, herr⟩ := fw_enhanced_wheel_rationals i
  have hp' : 0 < p := hp
  have hq' : 0 < q := hq
  have he' : 0 < e := he
  have hden : 0 < den := by dsimp [den]; positivity
  by_cases hPN : N ≤ P
  · have hdiv : ((q * (P - N) / den : ℕ) : ℝ) ≤ (q * (P - N) : ℕ) / (den : ℝ) := by
      exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := q * (P - N)) (n := den))
    have hsub : ((P - N : ℕ) : ℝ) = (P : ℝ) - N := Nat.cast_sub hPN
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq'
    have hppos : (0 : ℝ) < p := by exact_mod_cast hp'
    have hepos : (0 : ℝ) < e := by exact_mod_cast he'
    have hiden : ((q * (P - N) : ℕ) : ℝ) / den =
        ((((a : ℝ) / 5605287840000) * R - (1 / 2 + (c : ℝ) / e)) /
          ((p : ℝ) / q)) := by
      push_cast
      rw [hsub]
      dsimp [P, N, den]
      push_cast
      field_simp
      <;> ring
    have hrate := fw_enhanced_lower_rate j hj
    have hR : (0 : ℝ) ≤ R := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hrate hR
    have hreal : ((q * (P - N) / den : ℕ) : ℝ) ≤ fwFullStockEnhancedD i j R / 2 := by
      rw [hiden] at hdiv
      unfold fwFullStockEnhancedD fwAffineUniformStockThreshold
      rw [hrho, herr]
      dsimp [p, q, c, e, a] at *
      have hm := div_le_div_of_nonneg_right (show
        ((fwEnhancedLowerRate j : ℝ) / 5605287840000) * R -
            (1 / 2 + (fwEnhancedErrNum i : ℝ) / fwEnhancedErrDen i) ≤
        ((23 / 48 : ℝ) * fwFirstBandMu j - (6 / 69780 : ℝ) / fwFirstBandMu j) * R -
            (1 / 2 + (fwEnhancedErrNum i : ℝ) / fwEnhancedErrDen i) by linarith)
        (show 0 ≤ ((fwEnhancedRhoNum i : ℝ) / fwEnhancedRhoDen i) by positivity)
      have hn : (2 / ((fwEnhancedRhoNum i : ℝ) / fwEnhancedRhoDen i)) *
          (((23 / 48 : ℝ) * fwFirstBandMu j - (6 / 69780 : ℝ) / fwFirstBandMu j) * R -
            (1 / 2 + (fwEnhancedErrNum i : ℝ) / fwEnhancedErrDen i)) / 2 =
          (((23 / 48 : ℝ) * fwFirstBandMu j - (6 / 69780 : ℝ) / fwFirstBandMu j) * R -
            (1 / 2 + (fwEnhancedErrNum i : ℝ) / fwEnhancedErrDen i)) /
            ((fwEnhancedRhoNum i : ℝ) / fwEnhancedRhoDen i) := by ring
      rw [hn]
      exact hdiv.trans hm
    change q * (P - N) / den ≤ _
    exact Nat.le_floor hreal
  · have hz : P - N = 0 := Nat.sub_eq_zero_of_le (by omega)
    change q * (P - N) / den ≤ _
    simp [hz]

/-- The bound applies to any natural gap above the enhanced threshold; it
does not rely on parity. -/
theorem fw_enhanced_lower_increment_le_gap (i : Fin 8) {j R gap : ℕ}
    (hj : j ≤ 238) (hgap : fwFullStockEnhancedD i j R ≤ (gap : ℝ)) :
    2 * fwEnhancedLowerCount i j R ≤ gap := by
  by_cases hz : fwEnhancedLowerCount i j R = 0
  · simp [hz]
  · have hc := fw_enhanced_lower_count_le i j R hj
    have hfloorpos : 0 < ⌊fwFullStockEnhancedD i j R / 2⌋₊ := by omega
    have hDpos : 0 ≤ fwFullStockEnhancedD i j R / 2 := by
      have hp := Nat.floor_pos.mp hfloorpos
      linarith
    have hfloor := Nat.floor_le hDpos
    have hcR : (fwEnhancedLowerCount i j R : ℝ) ≤ ⌊fwFullStockEnhancedD i j R / 2⌋₊ := by exact_mod_cast hc
    have hR : ((2 * fwEnhancedLowerCount i j R : ℕ) : ℝ) ≤ gap := by push_cast; linarith
    exact_mod_cast hR

end
end Sude
