import Sude.FWAffineWheelPairSupply
import Sude.FWAffineMixedWheelCertificates

/-! A supplied screened stock and explicit AW gates for one source mixed wheel.
No gate discharge, growth trace or physical placement is asserted. -/
namespace Sude
noncomputable section

/-- All eight source wheels supply the exact discrepancy and unit conditions
for this conditional first-class affine candidate stage. -/
theorem fw_mixed_affine_common_gap_stage (i : Fin 8) {n : ℕ}
    (S : Finset ℕ) (R : ℕ) (L m mf eta : ℝ)
    (hR : 0 < R) (heven : 2 ∣ R) (hL : 0 < L)
    (hbefore : (R : ℝ) ≤ (poolMaximum n : ℝ) / L)
    (hS : S ⊆ (poolFinset n).filter (fun p => 43 < p))
    (heta : 0 < eta) (hmf : 0 < mf) (hm : mf ≤ m) (hstock : m ≤ S.card)
    (heps : 0 ≤ 1 / (2 * (1 + 1 / L)) - eta)
    (hshift : 0 < (R : ℝ) -
      fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta mf)
    (hslope : fwAffineSlope eta 2 m 1 (poolMaximum n) / fwMixedWheelRho i ≤ 1)
    (hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) * poolMaximum n ≤
      (1 / (2 * (1 + 1 / L)) - eta) * mf ^ 2) :
    let P := sameClassPairs S (progressionBinKey 0 R 2)
    let D := fwAffineThreshold 2 (fwMixedWheelRho i) eta m R 1 (poolMaximum n)
      (fwMixedWheelError i)
    0 < D ∧ D ≤ R ∧
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ D ≤ gap ∧
      (fwAffineSlope eta 2 m 1 (poolMaximum n) / fwMixedWheelRho i) *
        ((R : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta mf) ≤ gap ∧
      gap ≤ R ∧ 6 * (6 * (n + 8)) ≤ chosen.card ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ P) ∧
      (∀ p ∈ chosen, p ∈ S ∧ p + gap ∈ S) ∧
      pairFootprint chosen gap ⊆ S ∧ PairwiseDisjointPairs chosen gap := by
  dsimp only
  have hX : 0 < (poolMaximum n : ℝ) := by exact_mod_cast (poolMaximum_prime n).pos
  have hS' : ∀ p ∈ S, (p : ℝ) ≤ poolMaximum n ∧ p % 2 = 1 ∧
      Nat.Coprime p (fwMixedWheel i) := by
    intro p hp
    have hp' := fw_screened_pool_mixed_wheel_units hS p hp
    have hbound : (p : ℝ) ≤ poolMaximum n := by exact_mod_cast pool_le_poolMaximum hp'.1
    exact ⟨hbound, hp'.2.2.1, hp'.2.2.2 i⟩
  have hC : 0 ≤ fwMixedWheelError i :=
    fw_affine_discrepancy_nonneg (fw_mixed_wheel_affine_discrepancy i)
  have hthreshold := fw_affine_threshold_bounds (g := 2) (rho := fwMixedWheelRho i)
    (eta := eta) (M := m) (R := R) (r := 1) (X := poolMaximum n)
    (C := fwMixedWheelError i) (Mf := mf)
    (by norm_num) (fw_mixed_wheel_rho_pos i) heta (by norm_num) hX hC hmf hm hshift hslope
  obtain ⟨gap, chosen, hgap, hdiv, hmin, hmax, hcard, hpairs, havail, hmatching⟩ :=
    fw_affine_common_gap_from_bins S (fwMixedWheel i) R 6 (6 * (n + 8))
      (poolMaximum n) L m mf eta (fwMixedWheelRho i) (fwMixedWheelError i)
      (fw_mixed_wheel_pos_odd i).2 hR heven (by omega) hX hL hbefore hS'
      (fw_mixed_wheel_rho_pos i) heta hmf hm hstock heps hshift hslope
      (fw_mixed_wheel_affine_discrepancy i) hquota
  have hfoot : pairFootprint chosen gap ⊆ S := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (havail p hp).1
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact (havail q hq).2
  have hgain := hthreshold.2.2.trans hmin
  exact ⟨hthreshold.1, hthreshold.2.1, gap, chosen, hgap, hdiv, hmin, hgain,
    hmax, hcard, hpairs, havail, hfoot, hmatching⟩

end
end Sude
