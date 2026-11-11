import Sude.FWWheelCommonGap

/-! The source WW4/WW5 stock and rounding implication for supplied pairs.
See `problems/prime-line-sums/manuscripts/cutoff2_exact_wheel_window.md`
WW3, with `g=2`, `r=1`, and the exact floor. All stock, count and source
inequalities remain hypotheses; no growth trace is constructed. -/
namespace Sude
noncomputable section

/-- Source-real stock and actual pair lower bounds imply the weak integer
population gate. The `-N/2` bin term cancels the `-1/2` in the exact floor.
Here `c₀` is the supplied source bin coefficient and `c₀-η` its epsilon. -/
theorem fw_wheel_stock_floor_population_gate (N R z Q Pc : ℕ) (X m mf eta c₀ qbar : ℝ)
    (hX : 0 < X) (hmf : 0 ≤ mf) (hm : mf ≤ m) (heta : 0 ≤ eta)
    (heps : 0 ≤ c₀ - eta) (hstock : m * X ≤ N)
    (hA : 0 ≤ eta * m * R - 1 / 2)
    (hq : (Q : ℝ) ≤ qbar * X)
    (hW : 2 * (c₀ - eta) * mf ^ 2 ≥ 2 * (z : ℝ) * qbar)
    (hP : c₀ * (N : ℝ) ^ 2 * R / X - (N : ℝ) / 2 ≤ Pc)
    (heven : 2 ∣ R) :
    N * ⌊eta * m * R - 1 / 2⌋₊ + (R / 2) * (2 * (z * Q)) ≤ Pc := by
  have hm0 : 0 ≤ m := le_trans hmf hm
  have hN : 0 ≤ (N : ℝ) := by positivity
  have hR : 0 ≤ (R : ℝ) := by positivity
  have hz : 0 ≤ (z : ℝ) := by positivity
  have hc : 0 ≤ c₀ := by linarith
  have hstockmul := mul_le_mul_of_nonneg_left hstock hN
  have hratio : m * N ≤ (N : ℝ)^2 / X := by
    apply (le_div_iff₀ hX).2
    nlinarith
  have hmfstock : mf ^ 2 * X ≤ m * N := by
    have h1 := mul_nonneg (sub_nonneg.mpr hm) hmf
    have h2 := mul_nonneg (sub_nonneg.mpr hstock) hm0
    nlinarith [mul_nonneg h1 hX.le]
  have hsource : (z : ℝ) * Q ≤ (c₀ - eta) * mf ^ 2 * X := by
    have h1 := mul_le_mul_of_nonneg_left hq hz
    have h2 := mul_nonneg (show 0 ≤ 2 * (c₀ - eta) * mf ^ 2 - 2 * (z : ℝ) * qbar by linarith) hX.le
    nlinarith
  have htarget : (z : ℝ) * Q ≤ c₀ * (N : ℝ)^2 / X - eta * m * N := by
    have h1 := mul_le_mul_of_nonneg_left hratio hc
    have h2 := mul_le_mul_of_nonneg_left hmfstock heps
    simp only [div_eq_mul_inv] at h1 ⊢
    nlinarith
  have htargetR := mul_le_mul_of_nonneg_right htarget hR
  have hfloor := Nat.floor_le hA
  have hfloorN := mul_le_mul_of_nonneg_left hfloor hN
  have hreal : (N : ℝ) * (⌊eta * m * R - 1 / 2⌋₊ : ℝ) + (R : ℝ) * z * Q ≤ Pc := by
    simp only [div_eq_mul_inv] at htargetR hP
    nlinarith [htargetR, hfloorN, hP]
  have heq : (R / 2) * (2 * (z * Q)) = R * (z * Q) := by
    calc
      _ = ((R / 2) * 2) * (z * Q) := by ac_rfl
      _ = _ := by rw [Nat.div_mul_cancel heven]
  rw [heq]
  have hreal' : (N : ℝ) * (⌊eta * m * R - 1 / 2⌋₊ : ℝ) +
      (R : ℝ) * ((z * Q : ℕ) : ℝ) ≤ Pc := by
    simpa only [Nat.cast_mul, mul_assoc] using hreal
  exact_mod_cast hreal'

/-- The WW4 stock and actual pair-count premises yield the WW5 common-gap
matching directly, with the source's exact natural floor and no strict
numerical inequality. The existence of the supplied pair population and its
lower bound are separate obligations. -/
theorem fw_wheel_ww5_common_gap_from_stock
    (S : Finset ℕ) (P : Finset (ℕ × ℕ)) (W R z Q : ℕ)
    (X m mf eta c₀ qbar : ℝ)
    (hW : 0 < W) (hWodd : W % 2 = 1) (hR : 0 < R) (heven : 2 ∣ R)
    (hzQ : 0 < z * Q)
    (hS : ∀ p ∈ S, p % 2 = 1 ∧ Nat.Coprime p W)
    (hPvalid : ∀ x ∈ P, x.1 ∈ S ∧ x.2 ∈ S ∧ x.1 < x.2 ∧
      x.2 % 2 = x.1 % 2 ∧ x.2 - x.1 ≤ R)
    (hX : 0 < X) (hmf : 0 ≤ mf) (hm : mf ≤ m) (heta : 0 ≤ eta)
    (heps : 0 ≤ c₀ - eta) (hstock : m * X ≤ (S.card : ℝ))
    (hA : 0 ≤ eta * m * R - 1 / 2)
    (hq : (Q : ℝ) ≤ qbar * X)
    (hquota : 2 * (c₀ - eta) * mf ^ 2 ≥ 2 * (z : ℝ) * qbar)
    (hpairs : c₀ * (S.card : ℝ) ^ 2 * R / X - (S.card : ℝ) / 2 ≤ P.card) :
    let T := ⌊eta * m * R - 1 / 2⌋₊
    let k := fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
      (Nat.totient_pos.mpr hW)
    let h := 2 * min k (R / 2)
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ h ≤ gap ∧ gap ≤ R ∧ z * Q ≤ chosen.card ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ P) ∧
      (∀ p ∈ chosen, p ∈ S ∧ p + gap ∈ S) ∧ PairwiseDisjointPairs chosen gap := by
  dsimp only
  have hpop := fw_wheel_stock_floor_population_gate S.card R z Q P.card X m mf eta c₀ qbar
    hX hmf hm heta heps hstock hA hq hquota hpairs heven
  exact fw_wheel_ww5_common_gap_from_pair_population S P W _ R z Q hW hWodd hR
    heven hzQ hS hPvalid hpop


end
end Sude
