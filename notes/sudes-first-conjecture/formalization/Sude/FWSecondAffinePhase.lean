import Sude.FWFirstAffinePhase
import Sude.FWFirstWindowRadiusStrong

/-! Conditional second-wheel entry and continuation using a fresh origin and
fixed conservative mass. This does not establish crossing, later wheels,
physical growth placement, or the frozen varying-mass recipe. -/
namespace Sude
noncomputable section

/-- For the second mixed wheel, the fixed conservative mass yields an
origin strictly below 2196. The input mf is normalized and multiplied by X. -/
theorem fw_second_affine_origin_lt_2196 {X mf : ℝ}
    (hX : 0 < X) (hmf : (3257 / 100000 : ℝ) ≤ mf) :
    fwAffineOrigin (fwMixedWheelError 1) 1 X (3981035 / 10000000) (mf * X) < 2196 := by
  have hmfpos : 0 < mf := by linarith
  have heq : fwAffineOrigin (fwMixedWheelError 1) 1 X (3981035 / 10000000) (mf * X) =
      (1 / 2 + fwMixedWheelError 1) / ((3981035 / 10000000) * mf) := by
    unfold fwAffineOrigin
    field_simp
  rw [heq]
  apply (div_lt_iff₀ (show 0 < (3981035 / 10000000 : ℝ) * mf by positivity)).2
  norm_num [fwMixedWheelError]
  nlinarith

/-- The second mixed-wheel slope gate follows from the first-band mass
upper bound, for any positive X. -/
theorem fw_second_affine_slope_le_one {X m : ℝ}
    (hX : 0 < X) (hm : m ≤ (403 / 10000 : ℝ)) :
    fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 1 ≤ 1 := by
  have heq : fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 1 =
      (3981035 / 10000000 : ℝ) * 2 * m / fwMixedWheelRho 1 := by
    unfold fwAffineSlope
    field_simp
  rw [heq]
  norm_num [fwMixedWheelRho]
  linarith


/-- The actual witness stock after a supplied trace covers a fixed conservative mass plus
the exact reserved future deletion budget, up to the 238-stage envelope. -/
theorem fw_first_band_future_stock_budget
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (radius last fuel : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      radius final last stages)
    (hsteps : stages.length + fuel ≤ 238) :
    (3257 / 100000 : ℝ) * (poolMaximum n : ℝ) +
      ((2 * (6 * (n + 8)) * fuel : ℕ) : ℝ) ≤ (final.card : ℝ) := by
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
  have hj : ((stages.length : ℝ) + fuel) ≤ 238 := by exact_mod_cast hsteps
  have hqSteps := mul_le_mul_of_nonneg_left hq
    (show (0 : ℝ) ≤ 2 * ((stages.length : ℝ) + fuel) by positivity)
  have hcoef : (3257 / 100000 : ℝ) + 2 * (1 / 69780 : ℝ) *
      ((stages.length : ℝ) + fuel) ≤ 403 / 10000 := by linarith
  have hcoefX := mul_le_mul_of_nonneg_right hcoef hX.le
  push_cast at *
  nlinarith




theorem affine_schedule_radius_le {i : Fin 8} {n : ℕ} {L M Mf eta : ℝ}
    {R actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWMixedAffineCertifiedSchedule i n L M Mf eta R actual Rfinal actualFinal stages) :
    R ≤ Rfinal := by
  induction sched with
  | nil R actual => rfl
  | cons R actual Rfinal actualFinal stage tail hbefore hbelow hshift hminimum
      hpositive hgapEven hlower hupper hrest ih => omega

/-- On the second source wheel, continue the supplied trace up to eleven
additional stages, preserving the actual crossing-or-fuel alternative. -/
theorem fw_second_affine_phase_from_124
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (R last : ℕ) (S : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 S last stages)
    (hlen : stages.length ≤ 124) (hR : 7118 ≤ R) (heven : 2 ∣ R) (hbelow : R ≤ last) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    ∃ (final : Finset ℕ) (Rfinal lastFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final lastFinal (stages ++ extra) ∧
      extra.length ≤ 11 ∧ final ⊆ S ∧ final.card + 2 * Q * extra.length = S.card ∧
      (X / 23 ≤ lastFinal ∨ extra.length = 11) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages (X / 6) extra ∧
      R ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ lastFinal ∧
      FWMixedAffineCertifiedSchedule 1 n 23 M M eta R last Rfinal lastFinal extra := by
  dsimp only
  let X : ℝ := poolMaximum n
  let M : ℝ := (3257 / 100000 : ℝ) * X
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hM : 0 < M := by dsimp [M]; positivity
  have hRpos : 0 < R := by omega
  have horigin := fw_second_affine_origin_lt_2196 (X := X) (mf := (3257 / 100000 : ℝ)) hX (by norm_num)
  have hshift : 0 < (R : ℝ) - fwAffineOrigin (fwMixedWheelError 1) 1 X
      (3981035 / 10000000) M := by
    have hRreal : (7118 : ℝ) ≤ R := by exact_mod_cast hR
    dsimp [M]
    linarith
  have hslope : fwAffineSlope (3981035 / 10000000) 2 M 1 X / fwMixedWheelRho 1 ≤ 1 := by
    dsimp [M]
    exact fw_second_affine_slope_le_one hX (by norm_num)
  have hscreen : S ⊆ (poolFinset n).filter (fun p => 43 < p) :=
    trace.final_accounting.1.trans Finset.sdiff_subset
  have hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) * X ≤
      (1 / (2 * (1 + 1 / (23 : ℝ))) - 3981035 / 10000000) * M ^ 2 := by
    dsimp [M, X]
    convert fw_first_affine_absolute_quota bmor lower upper upperSharp hnlo hnhi using 1; norm_num
  have hbudget : M + ((2 * (6 * (n + 8)) * 11 : ℕ) : ℝ) ≤ S.card := by
    dsimp [M, X]
    exact fw_first_band_future_stock_budget bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last 11 S stages trace
      (by omega)
  obtain ⟨final, Rfinal, lastFinal, extra, htrace, hlen', hsub', hcard', hstop,
    hnarrow, hRfinal, heven', hbelow', hsched'⟩ :=
    fw_mixed_affine_iterate_bounded (1 : Fin 8) 11 trace 23 M M (3981035 / 10000000)
      hRpos heven hbelow (by norm_num) hscreen (by norm_num) hM (le_refl _) (by norm_num)
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


/-- The second affine phase inherits the stronger certified window radius
through any supplied first-wheel certified schedule. Wheel 1's origin must
still be recomputed; no change of origin is hidden in this inequality. -/
theorem fw_second_affine_entry_radius {n : ℕ} {R₀ last₀ R₁ last₁ : ℕ}
    {window first : List BTSelectedStage} {L M Mf eta : ℝ}
    (hwindow : FWFirstWindowCertifiedSchedule (poolMaximum n) 0 32 32 R₀ last₀ window)
    (hlen : window.length = 118)
    (hfirst : FWMixedAffineCertifiedSchedule 0 n L M Mf eta R₀ last₀ R₁ last₁ first) :
    7118 ≤ R₁ ∧ 2 ∣ R₁ ∧ R₁ ≤ last₁ := by
  have h₀ := fw_certified_118_radius_at_least_7118 hwindow hlen
  have hmono := affine_schedule_radius_le hfirst
  obtain ⟨heven, hbelow⟩ := fw_certified_schedule_endpoint_from_32 hwindow (by decide)
  obtain ⟨heven', hbelow'⟩ := fw_mixed_affine_schedule_endpoint hfirst heven hbelow
  exact ⟨h₀.trans hmono, heven', hbelow'⟩


/-- After a supplied complete certified 118-stage window schedule and six
same-mass first-wheel stages, start wheel 1 with a freshly checked origin.
It stops at actual crossing or after eleven further stages. -/
theorem fw_second_affine_phase_after_first
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (R₀ last₀ R₁ last₁ : ℕ) (S : Finset ℕ) (window first : List BTSelectedStage)
    (hwindow : FWFirstWindowCertifiedSchedule (poolMaximum n) 0 32 32 R₀ last₀ window)
    (hwindowlen : window.length = 118)
    (hfirst : FWMixedAffineCertifiedSchedule 0 n 23
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      (3981035 / 10000000) R₀ last₀ R₁ last₁ first)
    (hfirstlen : first.length = 6)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 S last₁ (window ++ first)) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    ∃ (final : Finset ℕ) (Rfinal lastFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final lastFinal ((window ++ first) ++ extra) ∧
      extra.length ≤ 11 ∧ final ⊆ S ∧ final.card + 2 * Q * extra.length = S.card ∧
      (X / 23 ≤ lastFinal ∨ extra.length = 11) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages (X / 6) extra ∧
      R₁ ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ lastFinal ∧
      FWMixedAffineCertifiedSchedule 1 n 23 M M eta R₁ last₁ Rfinal lastFinal extra := by
  have ⟨hR, heven, hbelow⟩ := fw_second_affine_entry_radius hwindow hwindowlen hfirst
  have hlen : (window ++ first).length ≤ 124 := by simp [hwindowlen, hfirstlen]
  exact fw_second_affine_phase_from_124 bmor lower upper upperSharp hnlo hnhi
    batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R₁ last₁ S
    (window ++ first) trace hlen hR heven hbelow


end
end Sude
