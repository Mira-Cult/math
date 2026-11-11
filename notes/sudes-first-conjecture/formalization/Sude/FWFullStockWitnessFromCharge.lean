import Sude.FWAffineUniformStockMatching
import Sude.FWFirstBandFullStockSlack
import Sude.FWAffineMixedWheelCertificates
import Sude.FWVaryingStockFromCharge

/-! First-band stronger affine matching from an explicit quota bound, on the same
supplied trace and early witnesses. The enhanced threshold is a selection guarantee; it need not itself
satisfy the frozen source's DR3 gate. No trace extension, physical placement,
or crossing is asserted. -/
namespace Sude
noncomputable section

/-- The stronger stock threshold yields actual disjoint candidates while the
original frozen-eta threshold stays strictly below their common gap. The
positivity of the enhanced threshold is the remaining radius condition. -/
theorem fw_first_band_full_stock_witness_common_gap_of_charge (i : Fin 8)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (hQ : ((6 * (n + 8) : ℕ) : ℝ) ≤ (1 / 69780 : ℝ) * (poolMaximum n : ℝ))
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (radius last R : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      radius final last stages)
    (hsteps : stages.length ≤ 238)
    (hR : 0 < R) (heven : 2 ∣ R)
    (hbefore : (R : ℝ) ≤ (poolMaximum n : ℝ) / 23)
    (hD : 0 < fwAffineUniformStockThreshold (fwFirstBandMu stages.length)
      (6 / 69780) R (23 / 48) (fwMixedWheelRho i) (fwMixedWheelError i)) :
    let X : ℝ := poolMaximum n
    let mu := fwFirstBandMu stages.length
    let D := fwAffineUniformStockThreshold mu (6 / 69780) R (23 / 48)
      (fwMixedWheelRho i) (fwMixedWheelError i)
    let Dsource := fwAffineThreshold 2 (fwMixedWheelRho i) (3981035 / 10000000)
      (mu * X) R 1 X (fwMixedWheelError i)
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ D ≤ gap ∧ Dsource < gap ∧ gap ≤ R ∧
      6 * (6 * (n + 8)) ≤ chosen.card ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ sameClassPairs final (progressionBinKey 0 R 2)) ∧
      (∀ p ∈ chosen, p ∈ final ∧ p + gap ∈ final) ∧
      pairFootprint chosen gap ⊆ final ∧
      Disjoint (pairFootprint chosen gap)
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) ∧
      PairwiseDisjointPairs chosen gap := by
  dsimp only
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hpool : final ⊆ (poolFinset n).filter (fun p => 43 < p) :=
    trace.final_accounting.1.trans Finset.sdiff_subset
  have hS : ∀ p ∈ final, (p : ℝ) ≤ poolMaximum n ∧ p % 2 = 1 ∧
      Nat.Coprime p (fwMixedWheel i) := by
    intro p hp
    have hp' := fw_screened_pool_mixed_wheel_units hpool p hp
    exact ⟨by exact_mod_cast pool_le_poolMaximum hp'.1, hp'.2.2.1, hp'.2.2.2 i⟩
  have hstock := fw_first_band_varying_stock_mass_of_charge upperSharp hnlo hnhi hQ
    batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks radius last final stages trace
  have hstock' : fwFirstBandMu stages.length * (poolMaximum n : ℝ) ≤ (final.card : ℝ) := by
    simpa only [← fw_first_band_mu_mass] using hstock
  have hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) ≤ (6 / 69780 : ℝ) * (poolMaximum n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hQ (show (0 : ℝ) ≤ 6 by norm_num)
    push_cast at h ⊢
    nlinarith
  have hmu := (fw_first_band_full_stock_quota_slack hsteps).2.1
  have hc0 : (1 / (2 * (1 + 1 / (23 : ℝ))) : ℝ) = 23 / 48 := by norm_num
  obtain ⟨gap, chosen, hgap, hdiv, hmin, hmax, hcard', hpairs, havail, hmatching⟩ :=
    fw_affine_uniform_stock_common_gap final (fwMixedWheel i) R 6 (6 * (n + 8))
      (poolMaximum n) 23 (fwMixedWheelRho i) (fwMixedWheelError i)
      (fwFirstBandMu stages.length) (6 / 69780)
      (fw_mixed_wheel_pos_odd i).2 hR heven (by omega) hX (by norm_num) hbefore hS
      (fw_mixed_wheel_rho_pos i) (fw_mixed_wheel_affine_discrepancy i) hmu (by norm_num)
      hstock' hquota (by rw [hc0]; exact hD)
  rw [hc0] at hmin
  have hstrict := fw_first_band_full_stock_threshold_strict (C := fwMixedWheelError i)
    hsteps hX hRreal (fw_mixed_wheel_rho_pos i)
  have hfoot : pairFootprint chosen gap ⊆ final := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (havail p hp).1
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact (havail q hq).2
  have hdisj : Disjoint (pairFootprint chosen gap)
      (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) := by
    apply Finset.disjoint_left.mpr
    intro p hp hpEarly
    have hinit := trace.final_accounting.1 (hfoot hp)
    exact (Finset.mem_sdiff.mp hinit).2 hpEarly
  refine ⟨gap, chosen, hgap, hdiv, ?_, ?_, hmax, hcard', hpairs, havail, hfoot, hdisj, hmatching⟩
  · exact hmin
  · exact hstrict.trans_le hmin

/-- At a certified large radius, the selected even gap exceeds the source
even increment by at least two; every original witness is preserved. -/
theorem fw_first_band_full_stock_witness_gap_above_increment_of_charge (i : Fin 8)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (hQ : ((6 * (n + 8) : ℕ) : ℝ) ≤ (1 / 69780 : ℝ) * (poolMaximum n : ℝ))
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (radius last R : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      radius final last stages)
    (hsteps : stages.length ≤ 238)
    (hR : 11648 ≤ R) (heven : 2 ∣ R)
    (hbefore : (R : ℝ) ≤ (poolMaximum n : ℝ) / 23)
    (hsource : 0 ≤ fwAffineThreshold 2 (fwMixedWheelRho i) (3981035 / 10000000)
      (fwFirstBandMu stages.length * (poolMaximum n : ℝ)) R 1 (poolMaximum n : ℝ)
      (fwMixedWheelError i))
    (hD : 0 < fwAffineUniformStockThreshold (fwFirstBandMu stages.length)
      (6 / 69780) R (23 / 48) (fwMixedWheelRho i) (fwMixedWheelError i)) :
    let X : ℝ := poolMaximum n
    let mu := fwFirstBandMu stages.length
    let D := fwAffineUniformStockThreshold mu (6 / 69780) R (23 / 48)
      (fwMixedWheelRho i) (fwMixedWheelError i)
    let Dsource := fwAffineThreshold 2 (fwMixedWheelRho i) (3981035 / 10000000)
      (mu * X) R 1 X (fwMixedWheelError i)
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ D ≤ gap ∧ Dsource < gap ∧
      2 * ⌈Dsource / 2⌉₊ + 2 ≤ gap ∧ gap ≤ R ∧
      6 * (6 * (n + 8)) ≤ chosen.card ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ sameClassPairs final (progressionBinKey 0 R 2)) ∧
      (∀ p ∈ chosen, p ∈ final ∧ p + gap ∈ final) ∧
      pairFootprint chosen gap ⊆ final ∧
      Disjoint (pairFootprint chosen gap)
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) ∧
      PairwiseDisjointPairs chosen gap := by
  dsimp only
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hRreal : (11648 : ℝ) ≤ R := by exact_mod_cast hR
  have hrho1 : fwMixedWheelRho i ≤ 1 := by
    fin_cases i <;> norm_num [fwMixedWheelRho]
  obtain ⟨gap, chosen, hgap, hdiv, hmin, hstrict, hmax, hcard', hpairs,
    havail, hfoot, hdisj, hmatching⟩ :=
    fw_first_band_full_stock_witness_common_gap_of_charge i upperSharp hnlo hnhi hQ
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks
      radius last R final stages trace hsteps (by omega) heven hbefore hD
  have hinc := fw_first_band_full_stock_gap_above_source_increment hsteps hX hRreal
    (fw_mixed_wheel_rho_pos i) hrho1 hsource hmin
  exact ⟨gap, chosen, hgap, hdiv, hmin, hstrict, hinc, hmax, hcard', hpairs,
    havail, hfoot, hdisj, hmatching⟩

/-- Source nonnegativity and the certified radius make the enhanced threshold
positive, preserving the same matching and two-unit increment conclusions. -/
theorem fw_first_band_full_stock_witness_gap_above_increment_of_charge_and_source_nonneg (i : Fin 8)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (hQ : ((6 * (n + 8) : ℕ) : ℝ) ≤ (1 / 69780 : ℝ) * (poolMaximum n : ℝ))
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (radius last R : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      radius final last stages)
    (hsteps : stages.length ≤ 238)
    (hR : 11648 ≤ R) (heven : 2 ∣ R)
    (hbefore : (R : ℝ) ≤ (poolMaximum n : ℝ) / 23)
    (hsource : 0 ≤ fwAffineThreshold 2 (fwMixedWheelRho i) (3981035 / 10000000)
      (fwFirstBandMu stages.length * (poolMaximum n : ℝ)) R 1 (poolMaximum n : ℝ)
      (fwMixedWheelError i))
    :
    let X : ℝ := poolMaximum n
    let mu := fwFirstBandMu stages.length
    let D := fwAffineUniformStockThreshold mu (6 / 69780) R (23 / 48)
      (fwMixedWheelRho i) (fwMixedWheelError i)
    let Dsource := fwAffineThreshold 2 (fwMixedWheelRho i) (3981035 / 10000000)
      (mu * X) R 1 X (fwMixedWheelError i)
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ D ≤ gap ∧ Dsource < gap ∧
      2 * ⌈Dsource / 2⌉₊ + 2 ≤ gap ∧ gap ≤ R ∧
      6 * (6 * (n + 8)) ≤ chosen.card ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ sameClassPairs final (progressionBinKey 0 R 2)) ∧
      (∀ p ∈ chosen, p ∈ final ∧ p + gap ∈ final) ∧
      pairFootprint chosen gap ⊆ final ∧
      Disjoint (pairFootprint chosen gap)
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) ∧
      PairwiseDisjointPairs chosen gap := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hRreal : (11648 : ℝ) ≤ R := by exact_mod_cast hR
  have hrho1 : fwMixedWheelRho i ≤ 1 := by
    fin_cases i <;> norm_num [fwMixedWheelRho]
  have hsep := fw_first_band_full_stock_threshold_add_three (C := fwMixedWheelError i)
    hsteps hX hRreal (fw_mixed_wheel_rho_pos i) hrho1
  have hD : 0 < fwAffineUniformStockThreshold (fwFirstBandMu stages.length)
      (6 / 69780) R (23 / 48) (fwMixedWheelRho i) (fwMixedWheelError i) := by
    linarith
  exact fw_first_band_full_stock_witness_gap_above_increment_of_charge i upperSharp
    hnlo hnhi hQ batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks
    radius last R final stages trace hsteps hR heven hbefore hsource hD

end
end Sude
