import Sude.FWEnhancedSeedRadiusUpper
import Sude.FWBT16IterationRadiusUpper
import Sude.FWBT16WidthCompare
import Sude.FWBT16TraceGrowth
import Sude.FWUpperBandsCrossing

/-! Screened crossing to `X/23` within 238 stages across `19485 ≤ n ≤ 35733`
    from explicit finite theta, RS, and Montgomery--Vaughan hypotheses,
    retaining the supplied early witnesses. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- The selected trace reaches X/23 within 238 stages: it either crosses
before the BT continuation, or actual-width BT stages force crossing.
The result concerns the screened trace, not physical installation or line sums. -/
theorem fw_enhanced_from_seed_bt16_crossing_of_theta_radius_upper
    (mv : MVBrunTitchmarsh)
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8))) :
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last stages ∧
      stages.length ≤ 238 ∧
      final ⊆ initial ∧
      final.card + 2 * (6 * (n + 8)) * stages.length = initial.card ∧
      stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) stages ∧
      (∀ stage ∈ stages, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      (poolMaximum n : ℝ) / 23 ≤ last ∧
      (last : ℝ) ≤ max (32 : ℝ) (2 * ((poolMaximum n : ℝ) / 23)) := by
  by_cases h21 : n ≤ 21248
  · dsimp only
    obtain ⟨stock, last, stages, trace, hcap, hsubstock, hcardstock, hnarrow, havoid, hstop, hupper⟩ :=
      fw_enhanced_from_seed_stop_or_complete_of_theta_radius_upper bmor lower upper upperSharp hnlo h21
        batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks
    rcases hstop with hcross | ⟨hcomplete, hlen, hlast⟩
    · exact ⟨stock, last, stages, trace, by omega, hsubstock, hcardstock,
        trace.pairwise_disjoint, hnarrow, havoid, hcross, hupper⟩
    · obtain ⟨final, last', extra, htrace, hsuffix, hextralen, htotal, hstop, hwidth,
        hnarrowExtra, hfinalsub, hfinalcard, hpairwise, havoidExtra, hupperExtra⟩ := by
        have hlog := fw_poolMaximum_log_gt_181_eighths lower hnlo
        have hratio := fw_actual_index_ratio_of_theta bmor lower upper hnlo (by omega)
        have hQ := fw_first_band_stage_charge_from_fw3 hnlo hlog hratio
        exact fw_bt16_chosen_iterate_first_band_radius_upper mv upperSharp hnlo h21 hQ
          batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 10 stock last stages trace
          (by omega) (by omega)
      have hcross : (poolMaximum n : ℝ) / 23 ≤ last' := by
        rcases hstop with hcross | hten
        · exact hcross
        · have hfixed := fw_bt16_varying_width_trace_fixed (by exact hwidth)
            (by omega : stages.length + extra.length ≤ 239) 0
          exact (fw_bt16_ten_width_stages_cross upperSharp hnlo h21 hsuffix hfixed hlast hten).le
      refine ⟨final, last', stages ++ extra, htrace, ?_, htrace.final_accounting.1,
        htrace.final_accounting.2.1, hpairwise, narrowed_append hnarrow hnarrowExtra, ?_, hcross,
        hupperExtra.trans (max_le hupper (le_max_right _ _))⟩
      · simpa using htotal
      · intro stage hs
        rcases List.mem_append.mp hs with hs | hs
        · exact havoid stage hs
        · exact havoidExtra stage hs
  · exact fw_upper_bands_crossing_of_theta_radius_upper mv bmor lower upper upperSharp
      (by omega) hnhi batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks

end
end Sude
