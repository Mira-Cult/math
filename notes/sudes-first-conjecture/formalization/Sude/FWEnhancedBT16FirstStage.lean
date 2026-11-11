import Sude.FWEnhancedBT16Entry
import Sude.FWBT16ChosenTrace
import Sude.FWActualIndexRatio

/-! Continue the enhanced first-band witness by one actual BT16 stage,
unless its 228-stage predecessor has already crossed. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- The same selected early witnesses produce either actual crossing or a
completed enhanced trace with one appended BT16 stage. The 6Q candidate
matching is narrowed to Q and only the retained 2Q endpoints are removed. -/
theorem fw_enhanced_from_seed_stop_or_first_bt16
    (mv : MVBrunTitchmarsh)
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidatesSeed : Finset ℕ) (hcard : candidatesSeed.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidatesSeed 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8))) :
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidatesSeed hcard kept hsub blocks
    ∃ (unused : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 unused last stages ∧
      unused ⊆ initial ∧
      unused.card + 2 * (6 * (n + 8)) * stages.length = initial.card ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) stages ∧
      (∀ stage ∈ stages, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidatesSeed hcard kept hsub blocks)) ∧
      ((poolMaximum n : ℝ) / 23 ≤ last ∨
        (FWEnhancedFromSeedComplete n last stages ∧ stages.length = 228 ∧
          174846346 ≤ last ∧
          fwFirstBandMu stages.length * (poolMaximum n : ℝ) ≤ (unused.card : ℝ) ∧
          ∃ (gap : ℕ) (candidates chosen : Finset ℕ),
            let Q := 6 * (n + 8)
            let D := 8 * ((3981035 / 10000000 : ℝ) * fwFirstBandMu stages.length * last - 1 / 2)
            0 < gap ∧ 2 ∣ gap ∧ gap ≤ last ∧ D ≤ gap ∧
            candidates.card = 6 * Q ∧ PairwiseDisjointPairs candidates gap ∧
            pairFootprint candidates gap ⊆ unused ∧ chosen ⊆ candidates ∧ chosen.card = Q ∧
            PairwiseDisjointPairs chosen gap ∧ pairFootprint chosen gap ⊆ unused ∧
            (pairFootprint chosen gap).card = 2 * Q ∧
            (unused \ pairFootprint chosen gap).card + 2 * Q = unused.card ∧
            (∀ p ∈ chosen, ∀ q ∈ chosen,
              |(((p : ℝ) + (p + gap : ℕ)) / 2) - (((q : ℝ) + (q + gap : ℕ)) / 2)| < (poolMaximum n : ℝ) / 6) ∧
            BTGrowingTrace 2 Q initial 32 (unused \ pairFootprint chosen gap) (last + gap)
              (stages ++ [⟨gap, chosen, D⟩]))) := by
  dsimp only
  obtain ⟨unused, last, stages, trace, hcap, hsubfinal, hcardfinal, hnarrow, havoid, hstop⟩ :=
    fw_enhanced_from_seed_stop_or_bt16_numeric_entry bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidatesSeed hcard kept hsub hkept hinj blocks hblocks
  refine ⟨unused, last, stages, trace, hsubfinal, hcardfinal, hnarrow, havoid, ?_⟩
  rcases hstop with hcross | ⟨hcomplete, hlen, hlast, hstock, hnorm, hwidth⟩
  · exact Or.inl hcross
  · by_cases hcross : (poolMaximum n : ℝ) / 23 ≤ last
    · exact Or.inl hcross
    · right
      refine ⟨hcomplete, hlen, hlast, hstock, ?_⟩
      have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
      have hratio := fw_actual_index_ratio bmor lower upper hnlo (by omega : n ≤ 35733)
      have hlog := fw_poolMaximum_log_gt_181_eighths lower hnlo
      have hQ := fw_first_band_stage_charge_from_fw3 hnlo hlog hratio
      have hscreen : unused ⊆ (poolFinset n).filter (fun p => 43 < p) := by
        intro p hp
        exact (Finset.mem_sdiff.mp (hsubfinal hp)).1
      have hunits := fw_screened_pool_mixed_wheel_units hscreen
      have hne : unused.Nonempty := by
        apply Finset.card_pos.mp
        have hmu := (fw_first_band_full_stock_quota_slack (j := stages.length) (by omega)).2.1
        have hpos : (0 : ℝ) < unused.card := lt_of_lt_of_le (mul_pos hmu hX) hstock
        exact_mod_cast hpos
      have hprimes : ∀ p ∈ unused, Nat.Prime p := by
        intro p hp
        exact (pool_prime_and_residue (hunits p hp).1).1
      have hclasses : ∀ p ∈ unused, p % 2 ∈ ({1} : Finset ℕ) := by
        intro p hp
        simpa using (hunits p hp).2.2.1
      have hreduced : ∀ a ∈ ({1} : Finset ℕ), 0 < a ∧ Nat.Coprime 2 a := by
        intro a ha
        have : a = 1 := by simpa using ha
        subst a
        decide
      have hle : ∀ p ∈ unused, (p : ℝ) ≤ poolMaximum n := by
        intro p hp
        exact_mod_cast pool_le_poolMaximum (hunits p hp).1
      exact trace.append_fw_bt16_first_band mv (poolMaximum n) last {1} (by omega) hX hQ
        (by omega) le_rfl (le_of_lt (lt_of_not_ge hcross)) hstock hne hprimes hclasses hreduced
        (by norm_num) hle

end
end Sude
