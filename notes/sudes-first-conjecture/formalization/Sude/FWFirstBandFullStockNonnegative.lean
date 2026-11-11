import Sude.FWFirstBandFullStockWitness

/-! Source-nonnegative specialization of the first-band strengthened selector.
No existence of the supplied trace, radius or source threshold is claimed. -/
namespace Sude
noncomputable section

/-- Source nonnegativity and the certified radius make the enhanced threshold
positive, preserving the same matching and two-unit increment conclusions. -/
theorem fw_first_band_full_stock_witness_gap_above_increment_of_source_nonneg (i : Fin 8)
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
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
  exact fw_first_band_full_stock_witness_gap_above_increment i bmor lower upper upperSharp
    hnlo hnhi batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks
    radius last R final stages trace hsteps hR heven hbefore hsource hD

end
end Sude
