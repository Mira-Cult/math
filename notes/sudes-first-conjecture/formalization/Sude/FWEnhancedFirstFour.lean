import Sude.FWEnhancedPhaseBounds
import Sude.FWFirstBandAffineComposition

/-! The first four enhanced fixed-wheel phases, with actual crossing checked
at each phase boundary. This does not assert that crossing occurs. -/
namespace Sude
noncomputable section

/-- The four linked full-stock phase schedules and their exact fuel lengths. -/
inductive FWEnhancedFourCompleted (n : ℕ) : ℕ → ℕ → List BTSelectedStage → Prop
  | mk (r0 r1 r2 r3 r4 : ℕ) (s0 s1 s2 s3 : List BTSelectedStage)
      (h0 : FWFullStockSchedule 0 n 118 r0 r1 s0) (l0 : s0.length = 6)
      (h1 : FWFullStockSchedule 1 n 124 r1 r2 s1) (l1 : s1.length = 11)
      (h2 : FWFullStockSchedule 2 n 135 r2 r3 s2) (l2 : s2.length = 12)
      (h3 : FWFullStockSchedule 3 n 147 r3 r4 s3) (l3 : s3.length = 9) :
      FWEnhancedFourCompleted n r0 r4 (((s0 ++ s1) ++ s2) ++ s3)

/-- From the same supplied first-band trace, construct enhanced phases through
wheel 3 unless the actual radius crosses earlier. The initial trace's length
and radius are explicit and no crossing or physical placement is claimed. -/
theorem fw_enhanced_first_four_stop_or_complete
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
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
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hs0 : 0 < (last : ℝ) - fwAffineOrigin (fwMixedWheelError 0) 1 (poolMaximum n)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) := by
    apply fw_indexed_affine_shift_of_radius 0 hX (by norm_num)
    change 1108 ≤ last
    omega
  obtain ⟨S0, r0, e0, ht0, le0, sub0, card0, stock0, stop0, narrow0, avoid0, grow0, even0, sched0⟩ :=
    fw_full_stock_iterate_bounded 0 bmor lower upper upperSharp hnlo hnhi batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks 6 last S stages trace (by omega) hlast hs0
  rcases stop0 with cross0 | len0
  · exact ⟨S0, r0, e0, ht0, by omega, sub0, card0, stock0, narrow0, avoid0, grow0, even0, Or.inl cross0⟩
  have sched0' : FWFullStockSchedule 0 n 118 last r0 e0 := by simpa [hlen] using sched0
  have br0 := fw_enhanced_phase_schedule_lower sched0' 11648 hlast
  rw [len0] at br0
  change fwEnhancedPhaseRun 0 118 6 11648 ≤ r0 at br0
  rw [fw_enhanced_phase0_boundary] at br0
  have hs1 : 0 < (r0 : ℝ) - fwAffineOrigin (fwMixedWheelError 1) 1 (poolMaximum n)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) := by
    apply fw_indexed_affine_shift_of_radius 1 hX (by norm_num)
    change 2196 ≤ r0
    omega
  obtain ⟨S1, r1, e1, ht1, le1, sub1, card1, stock1, stop1, narrow1, avoid1, grow1, even1, sched1⟩ :=
    fw_full_stock_iterate_bounded 1 bmor lower upper upperSharp hnlo hnhi batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks 11 r0 S0 (stages ++ e0) ht0
      (by simp [hlen, len0]) (by omega) hs1
  rcases stop1 with cross1 | len1
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
  have br1 := fw_enhanced_phase_schedule_lower sched1' 18262 br0
  rw [len1] at br1
  change fwEnhancedPhaseRun 1 124 11 18262 ≤ r1 at br1
  rw [fw_enhanced_phase1_boundary] at br1
  have hs2 : 0 < (r1 : ℝ) - fwAffineOrigin (fwMixedWheelError 2) 1 (poolMaximum n)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) := by
    apply fw_indexed_affine_shift_of_radius 2 hX (by norm_num)
    change 4380 ≤ r1
    omega
  obtain ⟨S2, r2, e2, ht2, le2, sub2, card2, stock2, stop2, narrow2, avoid2, grow2, even2, sched2⟩ :=
    fw_full_stock_iterate_bounded 2 bmor lower upper upperSharp hnlo hnhi batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks 12 r1 S1 ((stages ++ e0) ++ e1) ht1
      (by simp [hlen, len0, len1]) (by omega) hs2
  rcases stop2 with cross2 | len2
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
  have br2 := fw_enhanced_phase_schedule_lower sched2' 43062 br1
  rw [len2] at br2
  change fwEnhancedPhaseRun 2 135 12 43062 ≤ r2 at br2
  rw [fw_enhanced_phase2_boundary] at br2
  have hs3 : 0 < (r2 : ℝ) - fwAffineOrigin (fwMixedWheelError 3) 1 (poolMaximum n)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) := by
    apply fw_indexed_affine_shift_of_radius 3 hX (by norm_num)
    change 8747 ≤ r2
    omega
  obtain ⟨S3, r3, e3, ht3, le3, sub3, card3, stock3, stop3, narrow3, avoid3, grow3, even3, sched3⟩ :=
    fw_full_stock_iterate_bounded 3 bmor lower upper upperSharp hnlo hnhi batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks 9 r2 S2 (((stages ++ e0) ++ e1) ++ e2) ht2
      (by simp [hlen, len0, len1, len2]) (by omega) hs3
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
    · have br3 := fw_enhanced_phase_schedule_lower sched3' 114816 br2
      rw [len3] at br3
      change fwEnhancedPhaseRun 3 147 9 114816 ≤ r3 at br3
      rw [fw_enhanced_phase3_boundary] at br3
      right
      refine ⟨FWEnhancedFourCompleted.mk last r0 r1 r2 r3 e0 e1 e2 e3 sched0' len0 sched1' len1 sched2' len2 sched3' len3, ?_, br3⟩
      simp [len0, len1, len2, len3]

end
end Sude
