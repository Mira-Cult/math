import Sude.FWFirstWindowRadius118
import Sude.FWMixedAffineTraceStep
import Sude.FWWheelFirstBandTrace

/-! First affine-wheel entry after a supplied 118-stage certified window
trace. Numerical facts here do not prove further affine iterations or crossing. -/
namespace Sude
noncomputable section

/-- Wheel 0 origin using a normalized mass bound converted to absolute stock. -/
theorem fw_first_affine_origin_lt_1108 {X mf : ℝ}
    (hX : 0 < X) (hmf : (3257 / 100000 : ℝ) ≤ mf) :
    fwAffineOrigin (fwMixedWheelError 0) 1 X (3981035 / 10000000) (mf * X) < 1108 := by
  have hmfpos : 0 < mf := by linarith
  have heq : fwAffineOrigin (fwMixedWheelError 0) 1 X (3981035 / 10000000) (mf * X) =
      (1 / 2 + fwMixedWheelError 0) / ((3981035 / 10000000) * mf) := by
    unfold fwAffineOrigin
    field_simp
  rw [heq]
  apply (div_lt_iff₀ (show 0 < (3981035 / 10000000 : ℝ) * mf by positivity)).2
  norm_num [fwMixedWheelError]
  nlinarith

/-- A normalized mass upper bound certifies the wheel 0 slope gate. -/
theorem fw_first_affine_slope_le_one {X m : ℝ}
    (hX : 0 < X) (hm : m ≤ (403 / 10000 : ℝ)) :
    fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 0 ≤ 1 := by
  have heq : fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 0 =
      (3981035 / 10000000 : ℝ) * 2 * m / fwMixedWheelRho 0 := by
    unfold fwAffineSlope
    field_simp
  rw [heq]
  norm_num [fwMixedWheelRho]
  linarith

/-- The first-band terminal mass envelope has an explicit rational floor. -/
theorem fw_first_band_normalized_terminal_mass_floor {V : ℝ}
    (hVlo : (181 / 8 : ℝ) ≤ V) (hVhi : V ≤ 231 / 10) :
    (3257 / 100000 : ℝ) ≤ ((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V := by
  have hVpos : 0 < V := by linarith
  apply (le_div_iff₀ hVpos).2
  nlinarith

theorem fw_first_affine_normalized_quota_to_absolute
    {X Q qbar eps mf : ℝ} (hX : 0 < X) (hQ : Q ≤ qbar * X)
    (hE : 2 * eps * mf ^ 2 ≥ 2 * 6 * qbar) :
    6 * Q * X ≤ eps * (mf * X) ^ 2 := by
  have hx6 : 0 ≤ 6 * X := by positivity
  have hqmul := mul_le_mul_of_nonneg_left hQ hx6
  have heps : 6 * qbar ≤ eps * mf ^ 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_right heps (sq_nonneg X)
  nlinarith

/-- A supplied certified schedule preserves evenness and the order between
certified and actual radii. The initial order is required even for empty
schedules; this makes no crossing assertion. -/
theorem fw_certified_schedule_endpoint {X : ℝ}
    {j R actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWFirstWindowCertifiedSchedule X j R actual Rfinal actualFinal stages)
    (heven : 2 ∣ R) (hbelow : R ≤ actual) :
    2 ∣ Rfinal ∧ Rfinal ≤ actualFinal := by
  induction sched with
  | nil j R actual => exact ⟨heven, hbelow⟩
  | cons j R actual Rfinal actualFinal stage tail hcap hbefore hbelow' hfloor hminimum
      hpos hgapEven hgapLo hgapHi hrest ih =>
    apply ih
    · have hcut : 2 ∣ fwFirstWindowCutoff j R := by
        unfold fwFirstWindowCutoff
        exact dvd_mul_right 2 _
      exact dvd_add heven hcut
    · omega

/-- A radius-32 certified schedule starts even and cannot outgrow its
supplied actual radius. -/
theorem fw_certified_schedule_endpoint_from_32 {X : ℝ}
    {actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWFirstWindowCertifiedSchedule X 0 32 actual Rfinal actualFinal stages)
    (hbelow : 32 ≤ actual) : 2 ∣ Rfinal ∧ Rfinal ≤ actualFinal :=
  fw_certified_schedule_endpoint sched (by decide) hbelow


/-- First-band actual screened stock after any supplied trace of at most 238
stages, in absolute rather than normalized units. -/
theorem fw_first_band_witness_absolute_stock
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
    (hsteps : stages.length ≤ 238) :
    (3257 / 100000 : ℝ) * (poolMaximum n : ℝ) ≤ (final.card : ℝ) := by
  have hn : 13 ≤ n * n := by nlinarith
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  obtain ⟨hVlo, hVhi⟩ := fw_first_band_pointwise_log_bounds upperSharp lower hnlo hnhi
  obtain ⟨hbase, hq, _, _, _, _⟩ :=
    fw_first_band_ww4_envelopes_from_imports bmor lower upper upperSharp hnlo hnhi hsteps hVlo hVhi
  have hstock := (fw_wheel_witness_trace_stock hn batches hvalid candidates hcard kept hsub hkept
    hinj blocks hblocks radius last final stages trace).2.2.2.1
  have hstockR : ((n * n : ℕ) : ℝ) ≤ (final.card : ℝ) + fwEarlyBudget n + 13 +
      2 * ((6 * (n + 8) : ℕ) : ℝ) * stages.length := by exact_mod_cast hstock
  have hqSteps := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 2 * stages.length by positivity)
  have hj : (stages.length : ℝ) ≤ 238 := by exact_mod_cast hsteps
  have hcoef : (3257 / 100000 : ℝ) ≤ 403 / 10000 - 2 * (1 / 69780 : ℝ) * stages.length := by
    linarith
  have hcoefX := mul_le_mul_of_nonneg_right hcoef hX.le
  nlinarith


/-- Absolute AW quota from the first-band charge envelope, with a fixed
conservative normalized mass. No affine trace or origin is asserted. -/
theorem fw_first_affine_absolute_quota
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) :
    ((6 * (6 * (n + 8)) : ℕ) : ℝ) * (poolMaximum n : ℝ) ≤
      (23 / 48 - 3981035 / 10000000 : ℝ) *
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ)) ^ 2 := by
  have h := fw_first_band_ww4_envelopes_from_imports bmor lower upper upperSharp
    (n := n) (j := 118) (V := (181 / 8 : ℝ)) hnlo hnhi (by decide) (by norm_num) (by norm_num)
  dsimp only at h
  have hq := h.2.1
  have hx : (0 : ℝ) ≤ poolMaximum n := by positivity
  have hx2 : (0 : ℝ) ≤ (poolMaximum n : ℝ)^2 := sq_nonneg _
  have hc : (6 / 69780 : ℝ) ≤
      (23 / 48 - 3981035 / 10000000 : ℝ) * (3257 / 100000 : ℝ)^2 := by norm_num
  have hqX := mul_le_mul_of_nonneg_right hq hx
  have hcX := mul_le_mul_of_nonneg_right hc hx2
  push_cast at *
  nlinarith [hqX, hcX]


/-- A supplied noncrossing first-band trace that completed the certified
118-window schedule admits one first-wheel affine stage. The conservative
stock used for both AW masses is `(3257/100000)X`, an absolute count; it is
not asserted equal to the frozen recipe's mass. -/
theorem fw_first_band_first_affine_after_118
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (R last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 final last stages)
    (sched : FWFirstWindowCertifiedSchedule (poolMaximum n) 0 32 32 R last stages)
    (hlen : stages.length = 118)
    (hnotdone : (last : ℝ) < (poolMaximum n : ℝ) / 23) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    let P := sameClassPairs final (progressionBinKey 0 R 2)
    let D := fwAffineThreshold 2 (fwMixedWheelRho 0) eta M R 1 X (fwMixedWheelError 0)
    0 < D ∧ D ≤ R ∧
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ D ≤ gap ∧ gap ≤ R ∧ chosen.card = Q ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ P) ∧
      PairwiseDisjointPairs chosen gap ∧ pairFootprint chosen gap ⊆ final ∧
      Disjoint (pairFootprint chosen gap)
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) ∧
      (pairFootprint chosen gap).card = 2 * Q ∧
      (final \ pairFootprint chosen gap).card + 2 * Q = final.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + gap : ℕ)) / 2) - (((q : ℝ) + (q + gap : ℕ)) / 2)| < X / 6) ∧
      (1 + fwAffineSlope eta 2 M 1 X / fwMixedWheelRho 0) *
        ((R : ℝ) - fwAffineOrigin (fwMixedWheelError 0) 1 X eta M) ≤
          ((last + gap : ℕ) : ℝ) - fwAffineOrigin (fwMixedWheelError 0) 1 X eta M ∧
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 (final \ pairFootprint chosen gap) (last + gap)
        (stages ++ [⟨gap, chosen, D⟩]) := by
  dsimp only
  let X : ℝ := poolMaximum n
  let M : ℝ := (3257 / 100000 : ℝ) * X
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hM : 0 < M := by dsimp [M]; positivity
  have hlow : 1108 ≤ R := fw_certified_118_radius_at_least_1108 sched hlen
  obtain ⟨heven, hbelow⟩ := fw_certified_schedule_endpoint_from_32 sched (by decide)
  have hR : 0 < R := by omega
  have hbefore : (R : ℝ) ≤ X / 23 := by
    have hbelowR : (R : ℝ) ≤ last := by exact_mod_cast hbelow
    exact le_trans hbelowR (le_of_lt hnotdone)
  have hscreen : final ⊆ (poolFinset n).filter (fun p => 43 < p) :=
    trace.final_accounting.1.trans Finset.sdiff_subset
  have hstock : M ≤ (final.card : ℝ) := by
    dsimp [M, X]
    exact fw_first_band_witness_absolute_stock bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last final stages trace
      (by omega)
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
  obtain ⟨hD, hDR, gap, chosen, hgap, hdiv, hmin, hgain, hmax, hcard', hpairs,
    hmatch, hfoot, hsize, hdeplete, hmid, hradius, htrace⟩ :=
    fw_mixed_affine_append_stage (0 : Fin 8) trace 23 M M (3981035 / 10000000)
      hR heven hbelow (by norm_num) hbefore hscreen (by norm_num) hM (le_refl _) hstock
      (by norm_num) hshift hslope hquota
  have havoids : Disjoint (pairFootprint chosen gap)
      (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) := by
    apply Finset.disjoint_left.mpr
    intro p hp hearly
    exact (Finset.mem_sdiff.mp (trace.final_accounting.1 (hfoot hp))).2 hearly
  exact ⟨hD, hDR, gap, chosen, hgap, hdiv, hmin, hmax, hcard', hpairs,
    hmatch, hfoot, havoids, hsize, hdeplete, hmid, hradius, htrace⟩


end
end Sude
