import Sude.FWActualIndexRatio
import Sude.FWWheelFirstBandEnvelopes
import Sude.FWWheelFirstTraceStep

/-! Conservative first-band stock envelopes and one supplied trace step.
The q=4 prime-count and RS estimates are explicit hypotheses; neither a
preceding trace nor complete mixed FW recipe is asserted. -/
namespace Sude
noncomputable section

/-- The FW3 inequalities used by the conservative WW4 envelopes follow from
the stated published prime-count and RS hypotheses. V and the supplied stage
index remain explicit. -/
theorem fw_first_band_ww4_envelopes_from_imports
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n j : ℕ} {V : ℝ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hj : j ≤ 238)
    (hVlo : (181 / 8 : ℝ) ≤ V) (hVhi : V ≤ 231 / 10) :
    let X : ℝ := poolMaximum n
    let m₀ : ℝ := 403 / 10000
    let qbar : ℝ := 1 / 69780
    let mf : ℝ := ((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V
    let eps : ℝ := 23 / 48 - 3981035 / 10000000
    m₀ * X ≤ ((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n ∧
    ((6 * (n + 8) : ℕ) : ℝ) ≤ qbar * X ∧
    0 < mf ∧ mf ≤ m₀ - 2 * qbar * j ∧ 0 < eps ∧
    2 * eps * mf^2 ≥ 2 * 6 * qbar := by
  exact fw_first_band_ww4_envelopes upperSharp hnlo hnhi hj
    (fw_poolMaximum_log_gt_181_eighths lower hnlo)
    (fw_actual_index_ratio bmor lower upper hnlo (by omega)) hVlo hVhi

/-- A supplied trace with fewer than 238 stages admits one further first-wheel
stage when its certified radius is positive even, is below the actual radius,
and satisfies the explicit pre-crossing and floor conditions. The new stage
uses the same early witnesses and retains exactly Q narrowed pairs. -/
theorem fw_first_band_trace_first_window_append
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
    (hsteps : stages.length < 238) (V : ℝ)
    (hVlo : (181 / 8 : ℝ) ≤ V) (hVhi : V ≤ 231 / 10)
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
  dsimp only
  have hn : 13 ≤ n * n := by nlinarith
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  obtain ⟨hbase, hq, hmf, hm, heps, hquota⟩ :=
    fw_first_band_ww4_envelopes_from_imports bmor lower upper upperSharp hnlo hnhi
      (show stages.length ≤ 238 by omega) hVlo hVhi
  have hstepsR : (0 : ℝ) ≤ 2 * (stages.length : ℝ) := by positivity
  have hqSteps := mul_le_mul_of_nonneg_left hq hstepsR
  have hbound : ((403 / 10000 : ℝ) - 2 * (1 / 69780 : ℝ) * stages.length) ≤
      (((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n -
        2 * ((6 * (n + 8) : ℕ) : ℝ) * stages.length) / (poolMaximum n : ℝ) := by
    apply (le_div_iff₀ hX).2
    nlinarith
  exact fw_wheel_trace_first_window_append hn batches hvalid candidates hcard kept hsub hkept
    hinj blocks hblocks radius last final stages trace R 23
    ((403 / 10000 : ℝ) - 2 * (1 / 69780 : ℝ) * stages.length)
    (((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V)
    (3981035 / 10000000) (1 / 69780) hR heven hRlast (by norm_num) hnotdone
    hmf.le hm (by norm_num) (by norm_num) hbound hA hq
    (by norm_num at hquota ⊢; exact hquota)

end
end Sude
