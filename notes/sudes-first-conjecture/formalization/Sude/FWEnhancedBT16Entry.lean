import Sude.FWEnhancedInitialWindow
import Sude.FWBT16EntryGate
import Sude.FWFirstBandFullStockSlack

/-! The completed enhanced first-band branch pays the numerical lambda-16
BT start-width gate. No BT pair selection or subsequent stage is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- The same early-witness trace either reaches X/23 or completes the
228-stage enhanced construction and pays the capped numerical width gate
at its actual final radius, with the certified normalized stock lower bound.
This does not select any BT pairs. -/
theorem fw_enhanced_from_seed_stop_or_bt16_numeric_entry
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8))) :
    ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8))
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final last stages ∧
      stages.length ≤ 228 ∧
      final ⊆ (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) ∧
      final.card + 2 * (6 * (n + 8)) * stages.length =
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks).card ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) stages ∧
      (∀ stage ∈ stages, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      ((poolMaximum n : ℝ) / 23 ≤ last ∨
        (FWEnhancedFromSeedComplete n last stages ∧ stages.length = 228 ∧
          174846346 ≤ last ∧
          fwFirstBandMu stages.length * (poolMaximum n : ℝ) ≤ (final.card : ℝ) ∧
          (3257 / 100000 : ℝ) ≤ (final.card : ℝ) / (poolMaximum n : ℝ) ∧
          let D := 8 * ((3981035 / 10000000 : ℝ) * fwFirstBandMu stages.length * last - 1 / 2)
          Real.exp 16 ≤ min (last : ℝ) D / 2 ∧ 2 < D)) := by
  obtain ⟨final, last, stages, trace, hcap, hsubfinal, hcardfinal, hnarrow, havoid, hstop⟩ :=
    fw_enhanced_from_seed_stop_or_complete bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks
  refine ⟨final, last, stages, trace, hcap, hsubfinal, hcardfinal, hnarrow, havoid, ?_⟩
  rcases hstop with hcross | ⟨hcomplete, hlen, hlast⟩
  · exact Or.inl hcross
  · right
    have hmass := (fw_first_band_varying_stock_mass bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last final stages trace (by omega)).2
    have hstock : fwFirstBandMu stages.length * (poolMaximum n : ℝ) ≤ (final.card : ℝ) := by
      simpa only [fw_first_band_mu_mass] using hmass
    have hmu : (3257 / 100000 : ℝ) ≤ fwFirstBandMu stages.length := by
      have h := (fw_first_band_full_stock_quota_slack (j := stages.length) (by omega)).1
      linarith
    have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
    have hnorm : (3257 / 100000 : ℝ) ≤ (final.card : ℝ) / (poolMaximum n : ℝ) := by
      apply (le_div_iff₀ hX).2
      exact (mul_le_mul_of_nonneg_right hmu hX.le).trans hstock
    refine ⟨hcomplete, hlen, hlast, hstock, hnorm, ?_⟩
    exact fw_bt16_fixed_mass_capped_gate hmu (by omega)

end
end Sude
