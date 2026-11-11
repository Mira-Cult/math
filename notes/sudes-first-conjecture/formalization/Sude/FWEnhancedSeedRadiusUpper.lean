import Sude.FWEnhancedInitialWindow
import Sude.FWThetaCertifiedWindow
import Sude.FWEnhancedEightRadiusUpper

/-! Theta first-window and eight phases with a same-trace radius upper bound.
    The crossing alternative and all supplied early witnesses are retained. -/
namespace Sude
noncomputable section

/-- From the supplied early witnesses, construct an actual trace until it
crosses X/23 or completes the 118 first-window and 110 enhanced affine stages.
All analytic and witness assumptions remain explicit; no crossing is claimed. -/
theorem fw_enhanced_from_seed_stop_or_complete_of_theta_radius_upper
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
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
          174846346 ≤ last)) ∧
      (last : ℝ) ≤ max (32 : ℝ) (2 * ((poolMaximum n : ℝ) / 23)) := by
  let initial := ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
  obtain ⟨S0, R0, last0, window, htrace0, hlen0, hstop0, hnarrow0, _, _, _, hsched0⟩ :=
    fw_first_band_certified_first_window_bounded_stop_of_theta bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 32 initial []
      (BTGrowingTrace.nil _ _) (by simp) (by simp) (by norm_num) (by simp)
  simp only [List.nil_append, List.length_nil] at htrace0 hlen0 hstop0 hsched0
  change BTGrowingTrace 2 (6 * (n + 8)) (((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) 32 S0 last0 window at htrace0
  have havoid0 : ∀ stage ∈ window, Disjoint stage.footprint
      (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) := by
    intro stage hs
    apply Finset.disjoint_left.mpr
    intro p hp hearly
    exact (Finset.mem_sdiff.mp (htrace0.footprints_subset stage hs hp)).2 hearly
  have hupper0 := fw_first_window_schedule_radius_upper hsched0
  rcases hstop0 with hcross0 | hfull0
  · exact ⟨S0, last0, window, htrace0, by omega, htrace0.final_accounting.1,
      htrace0.final_accounting.2.1, hnarrow0, havoid0, Or.inl hcross0, hupper0⟩
  have hlast0 := fw_enhanced_completed_window_actual_lower hsched0 hfull0
  have hlog := fw_poolMaximum_log_gt_181_eighths lower hnlo
  have hratio := fw_actual_index_ratio_of_theta bmor lower upper hnlo (by omega)
  have hQ := fw_first_band_stage_charge_from_fw3 hnlo hlog hratio
  obtain ⟨final, last, extra, htrace, hlen, _, _, _, hnarrow, havoid, _, _, hstop, hupper⟩ :=
    fw_enhanced_eight_stop_or_complete_with_radius_upper upperSharp hnlo hnhi hQ batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks last0 S0 window htrace0 hfull0 hlast0
  refine ⟨final, last, window ++ extra, htrace, ?_, htrace.final_accounting.1,
    htrace.final_accounting.2.1, narrowed_append hnarrow0 hnarrow, ?_, ?_,
    hupper.trans (max_le hupper0 (le_max_right _ _))⟩
  · simp only [List.length_append]; omega
  · intro stage hs
    rcases List.mem_append.mp hs with hs | hs
    · exact havoid0 stage hs
    · exact havoid stage hs
  · rcases hstop with hcross | ⟨hcomplete, hlen', hbound⟩
    · exact Or.inl hcross
    · right
      exact ⟨FWEnhancedFromSeedComplete.mk R0 last0 window extra hsched0 hfull0 hcomplete,
        by simp [hfull0, hlen'], hbound⟩

end
end Sude
