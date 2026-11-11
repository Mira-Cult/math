import Sude.FWEnhancedFirstFour
import Sude.FWEnhancedSinglePhaseFromCharge

/-! Four linked enhanced phases from an explicitly supplied stage charge.
    Existing schedules, witnesses, stop alternatives and depletion remain. -/
namespace Sude
noncomputable section

/-- From the same supplied first-band trace, construct enhanced phases through
wheel 3 unless the actual radius crosses earlier. The initial trace's length
and radius are explicit and no crossing or physical placement is claimed. -/
theorem fw_enhanced_first_four_stop_or_complete_of_charge
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
    (hlen : stages.length = 118) (hlast : 11648 ≤ last) :
    ∃ (final : Finset ℕ) (last' : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8))
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final last' (stages ++ extra) ∧
      extra.length ≤ 38 ∧ final ⊆ S ∧
      final.card + 2 * (6 * (n + 8)) * extra.length = S.card ∧
      fwVaryingStockMass (poolMaximum n) (stages ++ extra).length ≤ (final.card : ℝ) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      last ≤ last' ∧ 2 ∣ last' ∧
      ((poolMaximum n : ℝ) / 23 ≤ last' ∨
        (FWEnhancedFourCompleted n last last' extra ∧ extra.length = 38 ∧ 245862 ≤ last')) := by
  obtain ⟨S0, r0, e0, ht0, le0, sub0, card0, stock0, stop0, narrow0, avoid0, grow0, even0, sched0⟩ :=
    fw_enhanced_single_phase_of_charge 0 upperSharp hnlo hnhi hQ batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks 6 last 11648 18262 S stages trace
      (by omega) (by norm_num) hlast (by decide)
      (by rw [hlen, fw_enhanced_phase0_boundary])
  rcases stop0 with cross0 | ⟨len0, br0⟩
  · exact ⟨S0, r0, e0, ht0, by omega, sub0, card0, stock0, narrow0, avoid0, grow0, even0, Or.inl cross0⟩
  have sched0' : FWFullStockSchedule 0 n 118 last r0 e0 := by simpa [hlen] using sched0
  obtain ⟨S1, r1, e1, ht1, le1, sub1, card1, stock1, stop1, narrow1, avoid1, grow1, even1, sched1⟩ :=
    fw_enhanced_single_phase_of_charge 1 upperSharp hnlo hnhi hQ batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks 11 r0 18262 43062 S0 (stages ++ e0) ht0
      (by simp [hlen, len0]) (by norm_num) br0 (by decide)
      (by simp [hlen, len0, fw_enhanced_phase1_boundary])
  rcases stop1 with cross1 | ⟨len1, br1⟩
  · refine ⟨S1, r1, e0 ++ e1, ?_, ?_, sub1.trans sub0, ?_, ?_,
      narrowed_append narrow0 narrow1, ?_, ?_, even1, Or.inl cross1⟩
    · simpa [List.append_assoc] using ht1
    · simp only [List.length_append]; omega
    · simp only [List.length_append]; rw [Nat.mul_add]; omega
    · simpa [List.append_assoc] using stock1
    · intro stage hs
      rcases List.mem_append.mp hs with hs | hs
      · exact avoid0 stage hs
      · exact avoid1 stage hs
    · omega
  have sched1' : FWFullStockSchedule 1 n 124 r0 r1 e1 := by simpa [hlen, len0] using sched1
  obtain ⟨S2, r2, e2, ht2, le2, sub2, card2, stock2, stop2, narrow2, avoid2, grow2, even2, sched2⟩ :=
    fw_enhanced_single_phase_of_charge 2 upperSharp hnlo hnhi hQ batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks 12 r1 43062 114816 S1 ((stages ++ e0) ++ e1) ht1
      (by simp [hlen, len0, len1]) (by norm_num) br1 (by decide)
      (by simp [hlen, len0, len1, fw_enhanced_phase2_boundary])
  rcases stop2 with cross2 | ⟨len2, br2⟩
  · refine ⟨S2, r2, (e0 ++ e1) ++ e2, ?_, ?_, sub2.trans (sub1.trans sub0), ?_, ?_,
      narrowed_append (narrowed_append narrow0 narrow1) narrow2, ?_, ?_, even2, Or.inl cross2⟩
    · simpa [List.append_assoc] using ht2
    · simp only [List.length_append]; omega
    · simp only [List.length_append]; rw [Nat.mul_add, Nat.mul_add]; omega
    · simpa [List.append_assoc] using stock2
    · intro stage hs
      rcases List.mem_append.mp hs with hs | hs
      · rcases List.mem_append.mp hs with hs | hs
        · exact avoid0 stage hs
        · exact avoid1 stage hs
      · exact avoid2 stage hs
    · omega
  have sched2' : FWFullStockSchedule 2 n 135 r1 r2 e2 := by simpa [hlen, len0, len1] using sched2
  obtain ⟨S3, r3, e3, ht3, le3, sub3, card3, stock3, stop3, narrow3, avoid3, grow3, even3, sched3⟩ :=
    fw_enhanced_single_phase_of_charge 3 upperSharp hnlo hnhi hQ batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks 9 r2 114816 245862 S2 (((stages ++ e0) ++ e1) ++ e2) ht2
      (by simp [hlen, len0, len1, len2]) (by norm_num) br2 (by decide)
      (by simp [hlen, len0, len1, len2, fw_enhanced_phase3_boundary])
  have sched3' : FWFullStockSchedule 3 n 147 r2 r3 e3 := by simpa [hlen, len0, len1, len2] using sched3
  have htailTrace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 S3 r3 (stages ++ (((e0 ++ e1) ++ e2) ++ e3)) := by simpa [List.append_assoc] using ht3
  have htailLen : (((e0 ++ e1) ++ e2) ++ e3).length ≤ 38 := by
    simp only [List.length_append]; omega
  have htailCard : S3.card + 2 * (6 * (n + 8)) * (((e0 ++ e1) ++ e2) ++ e3).length = S.card := by
    simp only [List.length_append]; rw [Nat.mul_add, Nat.mul_add, Nat.mul_add]; omega
  have htailStock : fwVaryingStockMass (poolMaximum n) (stages ++ (((e0 ++ e1) ++ e2) ++ e3)).length ≤ (S3.card : ℝ) := by
    simpa [List.append_assoc] using stock3
  have htailNarrow : NarrowedStages ((poolMaximum n : ℝ) / 6) (((e0 ++ e1) ++ e2) ++ e3) :=
    narrowed_append (narrowed_append (narrowed_append narrow0 narrow1) narrow2) narrow3
  have htailAvoid : ∀ stage ∈ (((e0 ++ e1) ++ e2) ++ e3), Disjoint stage.footprint
      (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) := by
    intro stage hs
    rcases List.mem_append.mp hs with hs | hs
    · rcases List.mem_append.mp hs with hs | hs
      · rcases List.mem_append.mp hs with hs | hs
        · exact avoid0 stage hs
        · exact avoid1 stage hs
      · exact avoid2 stage hs
    · exact avoid3 stage hs
  refine ⟨S3, r3, (((e0 ++ e1) ++ e2) ++ e3), htailTrace, htailLen,
    sub3.trans (sub2.trans (sub1.trans sub0)), htailCard, htailStock, htailNarrow,
    htailAvoid, ?_, even3, ?_⟩
  · omega
  · rcases stop3 with cross3 | len3
    · exact Or.inl cross3
    · rcases len3 with ⟨len3, br3⟩
      right
      refine ⟨FWEnhancedFourCompleted.mk last r0 r1 r2 r3 e0 e1 e2 e3 sched0' len0 sched1' len1 sched2' len2 sched3' len3, ?_, br3⟩
      simp [len0, len1, len2, len3]

end
end Sude
