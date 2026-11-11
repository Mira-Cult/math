import Sude.FWFirstAffineTransition
import Sude.FWMixedAffineIteration

/-! Conditional fixed-mass continuation for the first six-stage affine wheel.
This is a sufficient route from a supplied certified 118-window trace, not a
claim that the frozen varying-mass recipe or later phases are complete. -/
namespace Sude
noncomputable section

/-- The actual witness stock after at most 118 selected stages covers the
fixed conservative mass and six further `2Q` deletions. -/
theorem fw_first_affine_six_stage_stock_budget
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
    (hsteps : stages.length ≤ 118) :
    (3257 / 100000 : ℝ) * (poolMaximum n : ℝ) +
      ((2 * (6 * (n + 8)) * 6 : ℕ) : ℝ) ≤ (final.card : ℝ) := by
  have hn : 13 ≤ n * n := by nlinarith
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hbase := fw_first_band_stock_baseline upperSharp hnlo hnhi
  obtain ⟨hVlo, hVhi⟩ := fw_first_band_pointwise_log_bounds upperSharp lower hnlo hnhi
  have henv := fw_first_band_ww4_envelopes_from_imports bmor lower upper upperSharp hnlo hnhi
    (show stages.length ≤ 238 by omega) hVlo hVhi
  dsimp only at henv
  have hq := henv.2.1
  have hstock := (fw_wheel_witness_trace_stock hn batches hvalid candidates hcard kept hsub hkept
    hinj blocks hblocks radius last final stages trace).2.2.2.1
  have hstockR : ((n * n : ℕ) : ℝ) ≤ (final.card : ℝ) + fwEarlyBudget n + 13 +
      2 * ((6 * (n + 8) : ℕ) : ℝ) * stages.length := by exact_mod_cast hstock
  have hj : (stages.length : ℝ) ≤ 118 := by exact_mod_cast hsteps
  have hqSteps := mul_le_mul_of_nonneg_left hq
    (show (0 : ℝ) ≤ 2 * ((stages.length : ℝ) + 6) by positivity)
  have hcoef : (3257 / 100000 : ℝ) + 2 * (1 / 69780 : ℝ) *
      ((stages.length : ℝ) + 6) ≤ 403 / 10000 := by linarith
  have hcoefX := mul_le_mul_of_nonneg_right hcoef hX.le
  push_cast at *
  nlinarith


/-- Up to six fixed-mass first-wheel stages after a supplied certified
118-window trace. The stock budget is derived from the same early witnesses. -/
theorem fw_first_affine_phase_from_118
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (R last : ℕ) (S : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 S last stages)
    (sched : FWFirstWindowCertifiedSchedule (poolMaximum n) 0 32 32 R last stages)
    (hlen : stages.length = 118) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    ∃ (final : Finset ℕ) (Rfinal lastFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final lastFinal (stages ++ extra) ∧
      extra.length ≤ 6 ∧ final ⊆ S ∧ final.card + 2 * Q * extra.length = S.card ∧
      (X / 23 ≤ lastFinal ∨ extra.length = 6) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages (X / 6) extra ∧
      R ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ lastFinal ∧
      FWMixedAffineCertifiedSchedule 0 n 23 M M eta R last Rfinal lastFinal extra := by
  dsimp only
  let X : ℝ := poolMaximum n
  let M : ℝ := (3257 / 100000 : ℝ) * X
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hM : 0 < M := by dsimp [M]; positivity
  have hlow : 1108 ≤ R := fw_certified_118_radius_at_least_1108 sched hlen
  obtain ⟨heven, hbelow⟩ := fw_certified_schedule_endpoint_from_32 sched (by decide)
  have hR : 0 < R := by omega
  have hscreen : S ⊆ (poolFinset n).filter (fun p => 43 < p) :=
    trace.final_accounting.1.trans Finset.sdiff_subset
  have horigin := fw_first_affine_origin_lt_1108 (X := X) (mf := (3257 / 100000 : ℝ)) hX (by norm_num)
  have hshift : 0 < (R : ℝ) - fwAffineOrigin (fwMixedWheelError 0) 1 X
      (3981035 / 10000000) M := by
    have hlowR : (1108 : ℝ) ≤ R := by exact_mod_cast hlow
    dsimp [M]
    linarith
  have hslope : fwAffineSlope (3981035 / 10000000) 2 M 1 X / fwMixedWheelRho 0 ≤ 1 := by
    dsimp [M]
    exact fw_first_affine_slope_le_one hX (by norm_num)
  have hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) * X ≤
      (1 / (2 * (1 + 1 / (23 : ℝ))) - 3981035 / 10000000) * M ^ 2 := by
    dsimp [M, X]
    convert fw_first_affine_absolute_quota bmor lower upper upperSharp hnlo hnhi using 1; norm_num
  have hbudget : M + ((2 * (6 * (n + 8)) * 6 : ℕ) : ℝ) ≤ S.card := by
    dsimp [M, X]
    exact fw_first_affine_six_stage_stock_budget bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last S stages trace
      (by omega)
  obtain ⟨final, Rfinal, lastFinal, extra, htrace, hlen', hsub', hcard', hstop,
    hnarrow, hRfinal, heven', hbelow', hsched'⟩ :=
    fw_mixed_affine_iterate_bounded (0 : Fin 8) 6 trace 23 M M (3981035 / 10000000)
      hR heven hbelow (by norm_num) hscreen (by norm_num) hM (le_refl _) (by norm_num)
      hshift hslope hquota hbudget
  have havoids : ∀ stage ∈ extra, Disjoint stage.footprint
      (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) := by
    intro stage hstage
    apply Finset.disjoint_left.mpr
    intro p hp hearly
    have hmem := htrace.footprints_subset stage (List.mem_append.mpr (Or.inr hstage)) hp
    exact (Finset.mem_sdiff.mp hmem).2 hearly
  exact ⟨final, Rfinal, lastFinal, extra, htrace, hlen', hsub', hcard', hstop,
    havoids, hnarrow, hRfinal, heven', hbelow', hsched'⟩

end
end Sude
