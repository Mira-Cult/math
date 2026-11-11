import Sude.FWWheelFirstBandTrace

/-! Pointwise first-band logarithm envelopes and conditional first-wheel
append. The chosen V is log X itself, not the source's fixed band envelope.
The existing analytic inputs and the trace/radius/floor conditions remain explicit. -/
namespace Sude
noncomputable section

theorem fw_first_band_log_upper_of_rs (upper : RSIndexUpperSharp) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) :
    Real.log (poolMaximum n : ℝ) < (231 / 10 : ℝ) := by
  have hnR : (n : ℝ) ≤ 21248 := by exact_mod_cast hnhi
  have hnonneg : (0 : ℝ) ≤ n := by positivity
  have hX := fw_first_band_upper_index_ratio upper hnlo hnhi
  have hXpos : 0 < (poolMaximum n : ℝ) := by exact_mod_cast (poolMaximum_prime n).pos
  have hXcap : (poolMaximum n : ℝ) ≤ 5 * (2 : ℝ)^31 := by
    have hsquare : (n : ℝ)^2 ≤ (21248 : ℝ)^2 := pow_le_pow_left₀ hnonneg hnR 2
    have hm := mul_le_mul_of_nonneg_left hsquare (show (0 : ℝ) ≤ 22501 / 1000 by norm_num)
    have hmax : (22501 / 1000 : ℝ) * (21248 : ℝ)^2 ≤ 5 * (2 : ℝ)^31 := by norm_num
    exact hX.trans (hm.trans hmax)
  have hlog := Real.log_le_log hXpos hXcap
  rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (by positivity : (2 : ℝ)^31 ≠ 0),
      Real.log_pow] at hlog
  norm_num at hlog
  linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

theorem fw_first_band_pointwise_log_bounds (upper : RSIndexUpperSharp) (lower : RSIndexLower) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) :
    (181 / 8 : ℝ) ≤ Real.log (poolMaximum n : ℝ) ∧
      Real.log (poolMaximum n : ℝ) ≤ 231 / 10 :=
  ⟨(fw_poolMaximum_log_gt_181_eighths lower hnlo).le,
    (fw_first_band_log_upper_of_rs upper hnlo hnhi).le⟩
/-- The pointwise choice V=log X removes the independent V-range inputs
from the conditional first-band first-wheel append. This does not identify
V with the frozen source's band ceiling, nor construct the supplied trace. -/
theorem fw_first_band_trace_first_window_append_pointwise
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (radius last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      radius final last stages)
    (hsteps : stages.length < 238)
    (R : ℕ) (hR : 0 < R) (heven : 2 ∣ R) (hRlast : R ≤ last)
    (hnotdone : (last : ℝ) < (poolMaximum n : ℝ) / 23)
    (hA : 0 ≤ (3981035 / 10000000 : ℝ) *
      ((403 / 10000 : ℝ) - 2 * (1 / 69780 : ℝ) * stages.length) * R - 1 / 2) :
    let Q := 6 * (n + 8)
    let m : ℝ := 403 / 10000 - 2 * (1 / 69780 : ℝ) * stages.length
    let T := ⌊(3981035 / 10000000 : ℝ) * m * R - 1 / 2⌋₊
    let cutoff := 2 * min
      (fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
        (Nat.totient_pos.mpr (by decide))) (R / 2)
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ cutoff ≤ gap ∧ gap ≤ R ∧
      chosen.card = Q ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ sameClassPairs final (progressionBinKey 0 R 2)) ∧
      PairwiseDisjointPairs chosen gap ∧ pairFootprint chosen gap ⊆ final ∧
      Disjoint (pairFootprint chosen gap)
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) ∧
      (pairFootprint chosen gap).card = 2 * Q ∧
      (final \ pairFootprint chosen gap).card + 2 * Q = final.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + gap : ℕ)) / 2) - (((q : ℝ) + (q + gap : ℕ)) / 2)| <
          (poolMaximum n : ℝ) / 6) ∧
      R + cutoff ≤ last + gap ∧
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        radius (final \ pairFootprint chosen gap) (last + gap)
        (stages ++ [⟨gap, chosen, (cutoff : ℝ)⟩]) := by
  obtain ⟨hVlo, hVhi⟩ := fw_first_band_pointwise_log_bounds upperSharp lower hnlo hnhi
  exact fw_first_band_trace_first_window_append bmor lower upper upperSharp hnlo hnhi
    batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks radius last final stages
    trace hsteps (Real.log (poolMaximum n : ℝ)) hVlo hVhi R hR heven hRlast hnotdone hA

end
end Sude
