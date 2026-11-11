import Sude.FWAffineFullStockAlgebra
import Sude.FWAffineFullStockSelection

/-! Common-gap selection using all certified stock above a uniform envelope.
This is a single conditional selection; no stage, trace, crossing, or source
numerics are asserted. -/
namespace Sude
noncomputable section

/-- The normalized stock and quota envelopes imply an actual binned-pair gate
at D†. The strict AW2 bound leaves sufficient pairs even when the displayed
real inequalities hold at equality. The theorem needs no separate D† ≤ R
hypothesis: the resulting gap is at most R. -/
theorem fw_affine_uniform_stock_common_gap
    (S : Finset ℕ) (W R z Q : ℕ) (X L rho C mu b : ℝ)
    (hWodd : W % 2 = 1) (hR : 0 < R) (heven : 2 ∣ R)
    (hzQ : 0 < z * Q) (hX : 0 < X) (hL : 0 < L)
    (hbefore : (R : ℝ) ≤ X / L)
    (hS : ∀ p ∈ S, (p : ℝ) ≤ X ∧ p % 2 = 1 ∧ Nat.Coprime p W)
    (hrho : 0 < rho) (hdisc : FWAffineWheelDiscrepancy W rho C)
    (hmu : 0 < mu) (hb : 0 ≤ b)
    (hstock : mu * X ≤ (S.card : ℝ))
    (hquota : ((z * Q : ℕ) : ℝ) ≤ b * X)
    (hD : 0 < fwAffineUniformStockThreshold mu b R
      (1 / (2 * (1 + 1 / L))) rho C) :
    let P := sameClassPairs S (progressionBinKey 0 R 2)
    let D := fwAffineUniformStockThreshold mu b R
      (1 / (2 * (1 + 1 / L))) rho C
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ D ≤ gap ∧ gap ≤ R ∧ z * Q ≤ chosen.card ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ P) ∧
      (∀ p ∈ chosen, p ∈ S ∧ p + gap ∈ S) ∧ PairwiseDisjointPairs chosen gap := by
  dsimp only
  let N : ℝ := S.card
  let c0 : ℝ := 1 / (2 * (1 + 1 / L))
  let Z : ℝ := ((z * Q : ℕ) : ℝ)
  let D := fwAffineUniformStockThreshold mu b R c0 rho C
  let Dstar := fwAffineFullStockThreshold N R X c0 rho C Z
  have hNpos : 0 < N := lt_of_lt_of_le (mul_pos hmu hX) hstock
  have hne : S.Nonempty := Finset.card_pos.mp (by
    have hcard : (0 : ℝ) < (S.card : ℝ) := by simpa [N] using hNpos
    exact_mod_cast hcard)
  have hc0 : 0 ≤ c0 := by dsimp [c0]; positivity
  have hDle : D ≤ Dstar := fw_affine_uniform_stock_threshold_le_full hmu hb
    (by positivity : (0 : ℝ) ≤ R) hX hc0 hrho hstock hquota
  have hallow : N * (rho * D / 2 + C) ≤ N * (rho * Dstar / 2 + C) := by
    have h := mul_le_mul_of_nonneg_left hDle hrho.le
    have h' : rho * D / 2 + C ≤ rho * Dstar / 2 + C := by linarith
    exact mul_le_mul_of_nonneg_left h' hNpos.le
  have hcancel : N * (rho * Dstar / 2 + C) =
      c0 * N ^ 2 * R / X - N / 2 - Z * R :=
    fw_affine_full_stock_threshold_cancel (ne_of_gt hNpos) (ne_of_gt hX) (ne_of_gt hrho)
  have hgate : ((z * Q : ℕ) : ℝ) * R ≤
      (1 / (2 * (1 + 1 / L)) : ℝ) * (S.card : ℝ)^2 * R / X -
        (S.card : ℝ) / 2 - (S.card : ℝ) * (rho * D / 2 + C) := by
    dsimp [N, c0, Z] at hallow hcancel
    linarith
  exact fw_affine_common_gap_from_actual_stock_gate S W R z Q X L rho C D hne hWodd
    hR heven hzQ hX hL hbefore hS hrho hdisc hD hgate

end
end Sude
