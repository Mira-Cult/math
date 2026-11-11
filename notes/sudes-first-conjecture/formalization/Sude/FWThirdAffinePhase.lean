import Sude.FWSecondAffinePhase

namespace Sude
noncomputable section

/-- For the third mixed wheel, the fixed conservative mass yields an
origin strictly below 4380. The input mf is normalized and multiplied by X. -/
theorem fw_third_affine_origin_lt_4380 {X mf : ℝ}
    (hX : 0 < X) (hmf : (3257 / 100000 : ℝ) ≤ mf) :
    fwAffineOrigin (fwMixedWheelError 2) 1 X (3981035 / 10000000) (mf * X) < 4380 := by
  have hmfpos : 0 < mf := by linarith
  have heq : fwAffineOrigin (fwMixedWheelError 2) 1 X (3981035 / 10000000) (mf * X) =
      (1 / 2 + fwMixedWheelError 2) / ((3981035 / 10000000) * mf) := by
    unfold fwAffineOrigin
    field_simp
  rw [heq]
  apply (div_lt_iff₀ (show 0 < (3981035 / 10000000 : ℝ) * mf by positivity)).2
  norm_num [fwMixedWheelError, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  nlinarith

/-- The third mixed-wheel slope gate follows from the first-band mass
upper bound, for any positive X. -/
theorem fw_third_affine_slope_le_one {X m : ℝ}
    (hX : 0 < X) (hm : m ≤ (403 / 10000 : ℝ)) :
    fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 2 ≤ 1 := by
  have heq : fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 2 =
      (3981035 / 10000000 : ℝ) * 2 * m / fwMixedWheelRho 2 := by
    unfold fwAffineSlope
    field_simp
  rw [heq]
  norm_num [fwMixedWheelRho, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  linarith

/-- The third-wheel entry inherits the certified radius through both supplied
prior affine schedules. Each wheel's origin still needs a separate check. -/
theorem fw_third_affine_entry_radius {n : ℕ} {R₀ last₀ R₁ last₁ R₂ last₂ : ℕ}
    {window first second : List BTSelectedStage} {L M Mf eta : ℝ}
    (hwindow : FWFirstWindowCertifiedSchedule (poolMaximum n) 0 32 32 R₀ last₀ window)
    (hlen : window.length = 118)
    (hfirst : FWMixedAffineCertifiedSchedule 0 n L M Mf eta R₀ last₀ R₁ last₁ first)
    (hsecond : FWMixedAffineCertifiedSchedule 1 n L M Mf eta R₁ last₁ R₂ last₂ second) :
    7118 ≤ R₂ ∧ 2 ∣ R₂ ∧ R₂ ≤ last₂ := by
  obtain ⟨hlow, heven, hbelow⟩ := fw_second_affine_entry_radius hwindow hlen hfirst
  have hmono := affine_schedule_radius_le hsecond
  obtain ⟨heven', hbelow'⟩ := fw_mixed_affine_schedule_endpoint hsecond heven hbelow
  exact ⟨hlow.trans hmono, heven', hbelow'⟩


/-- On the third source wheel, continue the supplied trace up to twelve
additional stages, preserving the actual crossing-or-fuel alternative. -/
theorem fw_third_affine_phase_from_135
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
    (hlen : stages.length ≤ 135) (hR : 7118 ≤ R) (heven : 2 ∣ R) (hbelow : R ≤ last) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    ∃ (final : Finset ℕ) (Rfinal lastFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final lastFinal (stages ++ extra) ∧
      extra.length ≤ 12 ∧ final ⊆ S ∧ final.card + 2 * Q * extra.length = S.card ∧
      (X / 23 ≤ lastFinal ∨ extra.length = 12) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages (X / 6) extra ∧
      R ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ lastFinal ∧
      FWMixedAffineCertifiedSchedule 2 n 23 M M eta R last Rfinal lastFinal extra := by
  dsimp only
  let X : ℝ := poolMaximum n
  let M : ℝ := (3257 / 100000 : ℝ) * X
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hM : 0 < M := by dsimp [M]; positivity
  have hRpos : 0 < R := by omega
  have horigin := fw_third_affine_origin_lt_4380 (X := X) (mf := (3257 / 100000 : ℝ)) hX (by norm_num)
  have hshift : 0 < (R : ℝ) - fwAffineOrigin (fwMixedWheelError 2) 1 X
      (3981035 / 10000000) M := by
    have hRreal : (7118 : ℝ) ≤ R := by exact_mod_cast hR
    dsimp [M]
    linarith
  have hslope : fwAffineSlope (3981035 / 10000000) 2 M 1 X / fwMixedWheelRho 2 ≤ 1 := by
    dsimp [M]
    exact fw_third_affine_slope_le_one hX (by norm_num)
  have hscreen : S ⊆ (poolFinset n).filter (fun p => 43 < p) :=
    trace.final_accounting.1.trans Finset.sdiff_subset
  have hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) * X ≤
      (1 / (2 * (1 + 1 / (23 : ℝ))) - 3981035 / 10000000) * M ^ 2 := by
    dsimp [M, X]
    convert fw_first_affine_absolute_quota bmor lower upper upperSharp hnlo hnhi using 1; norm_num
  have hbudget : M + ((2 * (6 * (n + 8)) * 12 : ℕ) : ℝ) ≤ S.card := by
    dsimp [M, X]
    exact fw_first_band_future_stock_budget bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last 12 S stages trace
      (by omega)
  obtain ⟨final, Rfinal, lastFinal, extra, htrace, hlen', hsub', hcard', hstop,
    hnarrow, hRfinal, heven', hbelow', hsched'⟩ :=
    fw_mixed_affine_iterate_bounded (2 : Fin 8) 12 trace 23 M M (3981035 / 10000000)
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




/-- After a supplied complete certified 118-stage window schedule, six first-wheel stages and eleven second-wheel
stages, start wheel 2 with a freshly checked origin. It stops at actual
crossing or after twelve further stages. -/
theorem fw_third_affine_phase_after_second
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (R₀ last₀ R₁ last₁ R₂ last₂ : ℕ) (S : Finset ℕ) (window first second : List BTSelectedStage)
    (hwindow : FWFirstWindowCertifiedSchedule (poolMaximum n) 0 32 32 R₀ last₀ window)
    (hwindowlen : window.length = 118)
    (hfirst : FWMixedAffineCertifiedSchedule 0 n 23
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      (3981035 / 10000000) R₀ last₀ R₁ last₁ first)
    (hfirstlen : first.length = 6)
    (hsecond : FWMixedAffineCertifiedSchedule 1 n 23
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      (3981035 / 10000000) R₁ last₁ R₂ last₂ second)
    (hsecondlen : second.length = 11)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 S last₂ ((window ++ first) ++ second)) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    ∃ (final : Finset ℕ) (Rfinal lastFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final lastFinal (((window ++ first) ++ second) ++ extra) ∧
      extra.length ≤ 12 ∧ final ⊆ S ∧ final.card + 2 * Q * extra.length = S.card ∧
      (X / 23 ≤ lastFinal ∨ extra.length = 12) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages (X / 6) extra ∧
      R₂ ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ lastFinal ∧
      FWMixedAffineCertifiedSchedule 2 n 23 M M eta R₂ last₂ Rfinal lastFinal extra := by
  have ⟨hR, heven, hbelow⟩ := fw_third_affine_entry_radius hwindow hwindowlen hfirst hsecond
  have hlen : ((window ++ first) ++ second).length ≤ 135 := by simp [hwindowlen, hfirstlen, hsecondlen]
  exact fw_third_affine_phase_from_135 bmor lower upper upperSharp hnlo hnhi
    batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R₂ last₂ S
    ((window ++ first) ++ second) trace hlen hR heven hbelow




end
end Sude
