import Sude.FWMixedAffineStage
import Sude.FWWheelFirstTraceStep

namespace Sude
noncomputable section

/-- Under the explicit mixed-wheel AW gates, narrow one source candidate
matching to Q and append it to the supplied trace. No crossing, trace
existence, or physical placement is asserted. -/
theorem fw_mixed_affine_append_stage (i : Fin 8) {n R : ℕ}
    {initial S : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6 * (n + 8)) initial radius S last stages)
    (L m mf eta : ℝ)
    (hR : 0 < R) (heven : 2 ∣ R) (hRlast : R ≤ last) (hL : 0 < L)
    (hbefore : (R : ℝ) ≤ (poolMaximum n : ℝ) / L)
    (hS : S ⊆ (poolFinset n).filter (fun p => 43 < p))
    (heta : 0 < eta) (hmf : 0 < mf) (hm : mf ≤ m) (hstock : m ≤ S.card)
    (heps : 0 ≤ 1 / (2 * (1 + 1 / L)) - eta)
    (hshift : 0 < (R : ℝ) -
      fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta mf)
    (hslope : fwAffineSlope eta 2 m 1 (poolMaximum n) / fwMixedWheelRho i ≤ 1)
    (hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) * poolMaximum n ≤
      (1 / (2 * (1 + 1 / L)) - eta) * mf ^ 2) :
    let Q := 6 * (n + 8)
    let P := sameClassPairs S (progressionBinKey 0 R 2)
    let D := fwAffineThreshold 2 (fwMixedWheelRho i) eta m R 1 (poolMaximum n)
      (fwMixedWheelError i)
    0 < D ∧ D ≤ R ∧
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ D ≤ gap ∧
      (fwAffineSlope eta 2 m 1 (poolMaximum n) / fwMixedWheelRho i) *
        ((R : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta mf) ≤ gap ∧
      gap ≤ R ∧ chosen.card = Q ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ P) ∧
      PairwiseDisjointPairs chosen gap ∧ pairFootprint chosen gap ⊆ S ∧
      (pairFootprint chosen gap).card = 2 * Q ∧
      (S \ pairFootprint chosen gap).card + 2 * Q = S.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + gap : ℕ)) / 2) - (((q : ℝ) + (q + gap : ℕ)) / 2)| <
          (poolMaximum n : ℝ) / 6) ∧
      (1 + fwAffineSlope eta 2 m 1 (poolMaximum n) / fwMixedWheelRho i) *
        ((R : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta mf) ≤
          ((last + gap : ℕ) : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta mf ∧
      BTGrowingTrace 2 Q initial radius (S \ pairFootprint chosen gap) (last + gap)
        (stages ++ [⟨gap, chosen, D⟩]) := by
  dsimp only
  obtain ⟨hD, hDR, gap, candidates, hgap, hdiv, hmin, hgain, hmax, hcount,
    hpairs, havail, hfoot, hmatch⟩ :=
      fw_mixed_affine_common_gap_stage i S R L m mf eta hR heven hL hbefore hS
        heta hmf hm hstock heps hshift hslope hquota
  have hX : 0 < (poolMaximum n : ℝ) := by exact_mod_cast (poolMaximum_prime n).pos
  have hspan : ∀ p ∈ candidates, (0 : ℝ) ≤ p ∧
      (p : ℝ) < 0 + (6 : ℕ) * ((poolMaximum n : ℝ) / 6) := by
    intro p hp
    have hpnext : p + gap ∈ S := (havail p hp).2
    have hpPool := (fw_screened_pool_mixed_wheel_units hS (p + gap) hpnext).1
    have hbound : ((p + gap : ℕ) : ℝ) ≤ poolMaximum n := by
      exact_mod_cast pool_le_poolMaximum hpPool
    have hgap' : (0 : ℝ) < (gap : ℝ) := by exact_mod_cast hgap
    push_cast at hbound
    constructor <;> linarith
  obtain ⟨chosen, hsub, hcard, hm', hs, hf, hd, hnarrow, htrace⟩ :=
    trace.append_narrow_matching (z := 6) candidates gap
      (fwAffineThreshold 2 (fwMixedWheelRho i) eta m R 1 (poolMaximum n)
        (fwMixedWheelError i)) 0 ((poolMaximum n : ℝ) / 6)
      hgap hdiv (hmax.trans hRlast) hmin (by norm_num) (by positivity)
      hspan hcount hmatch hfoot
  have hradius : (1 + fwAffineSlope eta 2 m 1 (poolMaximum n) / fwMixedWheelRho i) *
      ((R : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta mf) ≤
        ((last + gap : ℕ) : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta mf := by
    have hRlast' : (R : ℝ) ≤ last := by exact_mod_cast hRlast
    push_cast
    nlinarith [hgain]
  refine ⟨hD, hDR, gap, chosen, hgap, hdiv, hmin, hgain, hmax, hcard, ?_,
    hm', hs, hf, hd, hnarrow, hradius, htrace⟩
  intro p hp
  exact hpairs p (hsub hp)

end
end Sude
