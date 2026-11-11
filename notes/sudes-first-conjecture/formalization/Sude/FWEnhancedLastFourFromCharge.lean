import Sude.FWEnhancedLastFour
import Sude.FWEnhancedSinglePhaseFromCharge

/-! Conditional continuation through the final four enhanced affine wheels.
The supplied trace and witnesses are not constructed by this module; crossing
is one possible result, not a conclusion. -/
namespace Sude
noncomputable section

private theorem fw_last_four_narrow_append {w : ℝ} {a b : List BTSelectedStage}
    (ha : NarrowedStages w a) (hb : NarrowedStages w b) : NarrowedStages w (a ++ b) := by
  intro stage hs
  rcases List.mem_append.mp hs with ha' | hb'
  · exact ha stage ha'
  · exact hb stage hb'

private theorem fw_last_four_avoid_append {V : Finset ℕ} {a b : List BTSelectedStage}
    (ha : ∀ stage ∈ a, Disjoint stage.footprint V)
    (hb : ∀ stage ∈ b, Disjoint stage.footprint V) :
    ∀ stage ∈ a ++ b, Disjoint stage.footprint V := by
  intro stage hs
  rcases List.mem_append.mp hs with ha' | hb'
  · exact ha stage ha'
  · exact hb stage hb'

/-- Continue a supplied 156-stage trace on wheels 4 through 7, with early
crossing retained. On the noncrossing branch all four phases are completed and
the actual radius is at least 174846346. -/
theorem fw_enhanced_last_four_stop_or_complete_of_charge
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (hQ : ((6 * (n + 8) : ℕ) : ℝ) ≤ (1 / 69780 : ℝ) * (poolMaximum n : ℝ))
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (last : ℕ) (S : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 S last stages)
    (hlen : stages.length = 156) (hlast : 245862 ≤ last) :
    ∃ (final : Finset ℕ) (last' : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8))
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final last' (stages ++ extra) ∧
      extra.length ≤ 72 ∧ final ⊆ S ∧
      final.card + 2 * (6 * (n + 8)) * extra.length = S.card ∧
      fwVaryingStockMass (poolMaximum n) (stages ++ extra).length ≤ (final.card : ℝ) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      last ≤ last' ∧ 2 ∣ last' ∧
      ((poolMaximum n : ℝ) / 23 ≤ last' ∨ FWEnhancedLastFourComplete n last last' extra) := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  obtain ⟨S4, r4, e4, ht4, le4, sub4, card4, stock4, stop4, narrow4, avoid4, grow4, even4, sched4⟩ :=
    fw_enhanced_single_phase_of_charge 4 upperSharp hnlo hnhi hQ batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks 10 last 245862 586810 S stages trace
      (by simp [hlen]) (by norm_num) hlast
      (by change 17479 ≤ 245862; norm_num)
      (by simp [hlen, fw_enhanced_phase4_boundary])
  rcases stop4 with cross4 | ⟨full4, b4⟩
  · exact ⟨S4, r4, e4, ht4, by omega, sub4, card4, stock4, narrow4, avoid4, grow4, even4, Or.inl cross4⟩
  obtain ⟨S5, r5, e5, ht5, le5, sub5, card5, stock5, stop5, narrow5, avoid5, grow5, even5, sched5⟩ :=
    fw_enhanced_single_phase_of_charge 5 upperSharp hnlo hnhi hQ batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks 10 r4 586810 1430864 S4 (stages ++ e4) ht4
      (by simp [hlen, full4]) (by norm_num) b4
      (by change 34942 ≤ 586810; norm_num)
      (by simp [hlen, full4, fw_enhanced_phase5_boundary])
  have nc45 := fw_last_four_narrow_append narrow4 narrow5
  have ac45 := fw_last_four_avoid_append avoid4 avoid5
  have cc45 : S5.card + 2 * (6 * (n + 8)) * (e4 ++ e5).length = S.card := by
    rw [List.length_append, Nat.mul_add]
    omega
  rcases stop5 with cross5 | ⟨full5, b5⟩
  · refine ⟨S5, r5, e4 ++ e5, ?_, ?_, sub5.trans sub4, cc45, ?_, nc45, ac45, ?_, even5, Or.inl cross5⟩
    · simpa [List.append_assoc] using ht5
    · simp; omega
    · simpa [List.append_assoc] using stock5
    · omega
  obtain ⟨S6, r6, e6, ht6, le6, sub6, card6, stock6, stop6, narrow6, avoid6, grow6, even6, sched6⟩ :=
    fw_enhanced_single_phase_of_charge 6 upperSharp hnlo hnhi hQ batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks 8 r5 1430864 2960558 S5 ((stages ++ e4) ++ e5) ht5
      (by simp [hlen, full4, full5]) (by norm_num) b5
      (by change 69868 ≤ 1430864; norm_num)
      (by simp [hlen, full4, full5, fw_enhanced_phase6_boundary])
  have nc456 := fw_last_four_narrow_append nc45 narrow6
  have ac456 := fw_last_four_avoid_append ac45 avoid6
  have cc456 : S6.card + 2 * (6 * (n + 8)) * ((e4 ++ e5) ++ e6).length = S.card := by
    rw [List.length_append, Nat.mul_add]
    omega
  rcases stop6 with cross6 | ⟨full6, b6⟩
  · refine ⟨S6, r6, (e4 ++ e5) ++ e6, ?_, ?_, sub6.trans (sub5.trans sub4), cc456,
      ?_, nc456, ac456, ?_, even6, Or.inl cross6⟩
    · simpa [List.append_assoc] using ht6
    · simp; omega
    · simpa [List.append_assoc] using stock6
    · omega
  obtain ⟨S7, r7, e7, ht7, le7, sub7, card7, stock7, stop7, narrow7, avoid7, grow7, even7, sched7⟩ :=
    fw_enhanced_single_phase_of_charge 7 upperSharp hnlo hnhi hQ batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks 44 r6 2960558 174846346 S6 (((stages ++ e4) ++ e5) ++ e6) ht6
      (by simp [hlen, full4, full5, full6]) (by norm_num) b6
      (by change 139718 ≤ 2960558; norm_num)
      (by simp [hlen, full4, full5, full6, fw_enhanced_phase7_boundary])
  have nc4567 := fw_last_four_narrow_append nc456 narrow7
  have ac4567 := fw_last_four_avoid_append ac456 avoid7
  have cc4567 : S7.card + 2 * (6 * (n + 8)) * (((e4 ++ e5) ++ e6) ++ e7).length = S.card := by
    rw [List.length_append, Nat.mul_add]
    omega
  rcases stop7 with cross7 | ⟨full7, b7⟩
  · refine ⟨S7, r7, ((e4 ++ e5) ++ e6) ++ e7, ?_, ?_, sub7.trans (sub6.trans (sub5.trans sub4)),
      cc4567, ?_, nc4567, ac4567, ?_, even7, Or.inl cross7⟩
    · simpa [List.append_assoc] using ht7
    · simp; omega
    · simpa [List.append_assoc] using stock7
    · omega
  have hsched4 : FWFullStockSchedule 4 n 156 last r4 e4 := by simpa [hlen] using sched4
  have hsched5 : FWFullStockSchedule 5 n 166 r4 r5 e5 := by simpa [hlen, full4] using sched5
  have hsched6 : FWFullStockSchedule 6 n 176 r5 r6 e6 := by simpa [hlen, full4, full5] using sched6
  have hsched7 : FWFullStockSchedule 7 n 184 r6 r7 e7 := by simpa [hlen, full4, full5, full6] using sched7
  refine ⟨S7, r7, ((e4 ++ e5) ++ e6) ++ e7, ?_, ?_, sub7.trans (sub6.trans (sub5.trans sub4)),
      cc4567, ?_, nc4567, ac4567, ?_, even7, Or.inr ?_⟩
  · simpa [List.append_assoc] using ht7
  · simp; omega
  · simpa [List.append_assoc] using stock7
  · omega
  · exact FWEnhancedLastFourComplete.mk r4 r5 r6 e4 e5 e6 e7 hsched4 full4 hsched5 full5
      hsched6 full6 hsched7 full7 b7

end
end Sude
