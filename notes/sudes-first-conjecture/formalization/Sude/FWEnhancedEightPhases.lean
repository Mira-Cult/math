import Sude.FWEnhancedFirstFour
import Sude.FWEnhancedLastFour

/-! Eight enhanced affine phases on a supplied first-band trace. Actual
crossing remains an alternative at every phase; no BT continuation or
physical placement is asserted. -/
namespace Sude
noncomputable section

/-- Both groups of four linked enhanced schedules have completed. -/
inductive FWEnhancedEightCompleted (n start finish : ℕ) : List BTSelectedStage → Prop
  | mk (middle : ℕ) (first last : List BTSelectedStage)
      (hfirst : FWEnhancedFourCompleted n start middle first)
      (hlast : FWEnhancedLastFourComplete n middle finish last) :
      FWEnhancedEightCompleted n start finish (first ++ last)

private theorem fw_enhanced_last_four_length {n start finish : ℕ}
    {stages : List BTSelectedStage} (h : FWEnhancedLastFourComplete n start finish stages) :
    stages.length = 72 := by
  cases h with
  | mk r1 r2 r3 s4 s5 s6 s7 h4 l4 h5 l5 h6 l6 h7 l7 hlower =>
    simp only [List.length_append, l4, l5, l6, l7]

private theorem fw_enhanced_last_four_endpoint {n start finish : ℕ}
    {stages : List BTSelectedStage} (h : FWEnhancedLastFourComplete n start finish stages) :
    174846346 ≤ finish := by
  cases h with
  | mk r1 r2 r3 s4 s5 s6 s7 h4 l4 h5 l5 h6 l6 h7 l7 hlower => exact hlower

/-- Continue all eight wheels from a supplied 118-stage first-band trace.
The trace, early witnesses and analytic assumptions are explicit. At every
phase actual crossing ends the construction; otherwise exactly 110 enhanced
stages are supplied with their linked schedules and a terminal radius bound. -/
theorem fw_enhanced_eight_stop_or_complete
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
      extra.length ≤ 110 ∧ final ⊆ S ∧
      final.card + 2 * (6 * (n + 8)) * extra.length = S.card ∧
      fwVaryingStockMass (poolMaximum n) (stages ++ extra).length ≤ (final.card : ℝ) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      last ≤ last' ∧ 2 ∣ last' ∧
      ((poolMaximum n : ℝ) / 23 ≤ last' ∨
        (FWEnhancedEightCompleted n last last' extra ∧ extra.length = 110 ∧
          174846346 ≤ last')) := by
  obtain ⟨S4, r4, first, ht4, le4, sub4, card4, stock4, narrow4, avoid4, grow4,
    even4, stop4⟩ :=
    fw_enhanced_first_four_stop_or_complete bmor lower upper upperSharp hnlo hnhi batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks last S stages trace hlen hlast
  rcases stop4 with cross4 | ⟨complete4, len4, bound4⟩
  · exact ⟨S4, r4, first, ht4, by omega, sub4, card4, stock4, narrow4, avoid4,
      grow4, even4, Or.inl cross4⟩
  obtain ⟨final, last', second, ht8, le8, sub8, card8, stock8, narrow8, avoid8, grow8,
    even8, stop8⟩ :=
    fw_enhanced_last_four_stop_or_complete bmor lower upper upperSharp hnlo hnhi batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks r4 S4 (stages ++ first) ht4
      (by simp [hlen, len4]) bound4
  refine ⟨final, last', first ++ second, ?_, ?_, sub8.trans sub4, ?_, ?_,
    narrowed_append narrow4 narrow8, ?_, ?_, even8, ?_⟩
  · simpa [List.append_assoc] using ht8
  · simp only [List.length_append]; omega
  · simp only [List.length_append]
    calc
      final.card + 2 * (6 * (n + 8)) * (first.length + second.length) =
          (final.card + 2 * (6 * (n + 8)) * second.length) +
            2 * (6 * (n + 8)) * first.length := by ring
      _ = S4.card + 2 * (6 * (n + 8)) * first.length := by rw [card8]
      _ = S.card := card4
  · simpa [List.append_assoc] using stock8
  · intro stage hs
    rcases List.mem_append.mp hs with hs | hs
    · exact avoid4 stage hs
    · exact avoid8 stage hs
  · omega
  · rcases stop8 with cross8 | complete8
    · exact Or.inl cross8
    · right
      have len8 := fw_enhanced_last_four_length complete8
      have bound8 := fw_enhanced_last_four_endpoint complete8
      exact ⟨FWEnhancedEightCompleted.mk r4 first second complete4 complete8,
        by simp [len4, len8], bound8⟩

end
end Sude
