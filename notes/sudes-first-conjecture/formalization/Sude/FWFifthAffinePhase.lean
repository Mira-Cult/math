import Sude.FWFourthAffinePhase

namespace Sude
noncomputable section

/-- For the fifth mixed wheel, the fixed conservative mass yields an
origin strictly below 17479. The input mf is normalized and multiplied by X. -/
theorem fw_fifth_affine_origin_lt_17479 {X mf : ℝ}
    (hX : 0 < X) (hmf : (3257 / 100000 : ℝ) ≤ mf) :
    fwAffineOrigin (fwMixedWheelError 4) 1 X (3981035 / 10000000) (mf * X) < 17479 := by
  have hmfpos : 0 < mf := by linarith
  have heq : fwAffineOrigin (fwMixedWheelError 4) 1 X (3981035 / 10000000) (mf * X) =
      (1 / 2 + fwMixedWheelError 4) / ((3981035 / 10000000) * mf) := by
    unfold fwAffineOrigin
    field_simp
  rw [heq]
  apply (div_lt_iff₀ (show 0 < (3981035 / 10000000 : ℝ) * mf by positivity)).2
  norm_num [fwMixedWheelError, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  nlinarith

/-- The fifth mixed-wheel slope gate follows from the first-band mass
upper bound, for any positive X. -/
theorem fw_fifth_affine_slope_le_one {X m : ℝ}
    (hX : 0 < X) (hm : m ≤ (403 / 10000 : ℝ)) :
    fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 4 ≤ 1 := by
  have heq : fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 4 =
      (3981035 / 10000000 : ℝ) * 2 * m / fwMixedWheelRho 4 := by
    unfold fwAffineSlope
    field_simp
  rw [heq]
  norm_num [fwMixedWheelRho, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
  linarith

/-- A uniform lower bound for the second-wheel source threshold. -/
theorem fw_second_threshold_at_9710 (n : ℕ) :
    (569 : ℝ) ≤ fwAffineThreshold 2 (fwMixedWheelRho 1)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) 9710 1
      (poolMaximum n) (fwMixedWheelError 1) := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have heq : fwAffineThreshold 2 (fwMixedWheelRho 1)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) 9710 1
      (poolMaximum n) (fwMixedWheelError 1) =
      2 / fwMixedWheelRho 1 * ((3981035 / 10000000 : ℝ) * (3257 / 100000) * 9710 -
        (1 / 2 + fwMixedWheelError 1)) := by
    unfold fwAffineThreshold
    field_simp
  rw [heq]
  norm_num [fwMixedWheelRho, fwMixedWheelError]

/-- A uniform lower bound for the third-wheel source threshold. -/
theorem fw_third_threshold_at_15969 (n : ℕ) :
    (918 : ℝ) ≤ fwAffineThreshold 2 (fwMixedWheelRho 2)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) 15969 1
      (poolMaximum n) (fwMixedWheelError 2) := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have heq : fwAffineThreshold 2 (fwMixedWheelRho 2)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) 15969 1
      (poolMaximum n) (fwMixedWheelError 2) =
      2 / fwMixedWheelRho 2 * ((3981035 / 10000000 : ℝ) * (3257 / 100000) * 15969 -
        (1 / 2 + fwMixedWheelError 2)) := by
    unfold fwAffineThreshold
    field_simp
  rw [heq]
  norm_num [fwMixedWheelRho, fwMixedWheelError, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem fw_second_eleven_radius {n R actual Rfinal actualFinal : ℕ}
    {stages : List BTSelectedStage}
    (sched : FWMixedAffineCertifiedSchedule 1 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n)
      ((3257 / 100000 : ℝ) * poolMaximum n) (3981035 / 10000000)
      R actual Rfinal actualFinal stages)
    (hR : 9710 ≤ R) (hlen : stages.length = 11) : 15969 ≤ Rfinal := by
  have hM : (0 : ℝ) ≤ (3257 / 100000 : ℝ) * poolMaximum n := by positivity
  have hg := fw_affine_schedule_linear_growth_from_floor (k := 569) (Rmin := 9710)
    sched hR (by norm_num) hM (fw_second_threshold_at_9710 n)
  rw [hlen] at hg
  omega

theorem fw_third_twelve_radius {n R actual Rfinal actualFinal : ℕ}
    {stages : List BTSelectedStage}
    (sched : FWMixedAffineCertifiedSchedule 2 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n)
      ((3257 / 100000 : ℝ) * poolMaximum n) (3981035 / 10000000)
      R actual Rfinal actualFinal stages)
    (hR : 15969 ≤ R) (hlen : stages.length = 12) : 26985 ≤ Rfinal := by
  have hM : (0 : ℝ) ≤ (3257 / 100000 : ℝ) * poolMaximum n := by positivity
  have hg := fw_affine_schedule_linear_growth_from_floor (k := 918) (Rmin := 15969)
    sched hR (by norm_num) hM (fw_third_threshold_at_15969 n)
  rw [hlen] at hg
  omega

/-- Completed prior schedules provide the next certified radius and reset gate. -/
theorem fw_fifth_entry_radius {n : ℕ} {R₀ last₀ R₁ last₁ R₂ last₂ R₃ last₃ R₄ last₄ : ℕ}
    {window first second third fourth : List BTSelectedStage}
    (hwindow : FWFirstWindowCertifiedSchedule (poolMaximum n) 0 32 32 R₀ last₀ window)
    (hlen : window.length = 118)
    (hfirst : FWMixedAffineCertifiedSchedule 0 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n) ((3257 / 100000 : ℝ) * poolMaximum n)
      (3981035 / 10000000) R₀ last₀ R₁ last₁ first)
    (hfirstlen : first.length = 6)
    (hsecond : FWMixedAffineCertifiedSchedule 1 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n) ((3257 / 100000 : ℝ) * poolMaximum n)
      (3981035 / 10000000) R₁ last₁ R₂ last₂ second)
    (hsecondlen : second.length = 11)
    (hthird : FWMixedAffineCertifiedSchedule 2 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n) ((3257 / 100000 : ℝ) * poolMaximum n)
      (3981035 / 10000000) R₂ last₂ R₃ last₃ third)
    (hthirdlen : third.length = 12)
    (hfourth : FWMixedAffineCertifiedSchedule 3 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n) ((3257 / 100000 : ℝ) * poolMaximum n)
      (3981035 / 10000000) R₃ last₃ R₄ last₄ fourth) :
    26985 ≤ R₄ ∧ 2 ∣ R₄ ∧ R₄ ≤ last₄ ∧
      fwAffineOrigin (fwMixedWheelError 4) 1 (poolMaximum n) (3981035 / 10000000)
        ((3257 / 100000 : ℝ) * poolMaximum n) < R₄ := by
  have hR₀ := fw_certified_118_radius_at_least_7118 hwindow hlen
  have hR₁ := fw_six_first_affine_stages_radius_9710 hfirst hR₀ hfirstlen
  have hR₂ := fw_second_eleven_radius hsecond hR₁ hsecondlen
  have hR₃ := fw_third_twelve_radius hthird hR₂ hthirdlen
  have hR₄ := hR₃.trans (affine_schedule_radius_le hfourth)
  obtain ⟨heven, hbelow⟩ := fw_certified_schedule_endpoint_from_32 hwindow (by decide)
  obtain ⟨heven₁, hbelow₁⟩ := fw_mixed_affine_schedule_endpoint hfirst heven hbelow
  obtain ⟨heven₂, hbelow₂⟩ := fw_mixed_affine_schedule_endpoint hsecond heven₁ hbelow₁
  obtain ⟨heven₃, hbelow₃⟩ := fw_mixed_affine_schedule_endpoint hthird heven₂ hbelow₂
  obtain ⟨heven₄, hbelow₄⟩ := fw_mixed_affine_schedule_endpoint hfourth heven₃ hbelow₃
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have horigin := fw_fifth_affine_origin_lt_17479 (X := poolMaximum n)
    (mf := (3257 / 100000 : ℝ)) hX (by norm_num)
  have hR₄real : (26985 : ℝ) ≤ R₄ := by exact_mod_cast hR₄
  exact ⟨hR₄, heven₄, hbelow₄, by linarith⟩

/-- On the fifth source wheel, continue the supplied trace up to ten
additional stages, preserving the actual crossing-or-fuel alternative. -/
theorem fw_fifth_affine_phase_from_156
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
    (hlen : stages.length ≤ 156) (hR : 26985 ≤ R) (heven : 2 ∣ R) (hbelow : R ≤ last) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    ∃ (final : Finset ℕ) (Rfinal lastFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final lastFinal (stages ++ extra) ∧
      extra.length ≤ 10 ∧ final ⊆ S ∧ final.card + 2 * Q * extra.length = S.card ∧
      (X / 23 ≤ lastFinal ∨ extra.length = 10) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages (X / 6) extra ∧
      R ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ lastFinal ∧
      FWMixedAffineCertifiedSchedule 4 n 23 M M eta R last Rfinal lastFinal extra := by
  dsimp only
  let X : ℝ := poolMaximum n
  let M : ℝ := (3257 / 100000 : ℝ) * X
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hM : 0 < M := by dsimp [M]; positivity
  have hRpos : 0 < R := by omega
  have horigin := fw_fifth_affine_origin_lt_17479 (X := X) (mf := (3257 / 100000 : ℝ)) hX (by norm_num)
  have hshift : 0 < (R : ℝ) - fwAffineOrigin (fwMixedWheelError 4) 1 X
      (3981035 / 10000000) M := by
    have hRreal : (26985 : ℝ) ≤ R := by exact_mod_cast hR
    dsimp [M]
    linarith
  have hslope : fwAffineSlope (3981035 / 10000000) 2 M 1 X / fwMixedWheelRho 4 ≤ 1 := by
    dsimp [M]
    exact fw_fifth_affine_slope_le_one hX (by norm_num)
  have hscreen : S ⊆ (poolFinset n).filter (fun p => 43 < p) :=
    trace.final_accounting.1.trans Finset.sdiff_subset
  have hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) * X ≤
      (1 / (2 * (1 + 1 / (23 : ℝ))) - 3981035 / 10000000) * M ^ 2 := by
    dsimp [M, X]
    convert fw_first_affine_absolute_quota bmor lower upper upperSharp hnlo hnhi using 1; norm_num
  have hbudget : M + ((2 * (6 * (n + 8)) * 10 : ℕ) : ℝ) ≤ S.card := by
    dsimp [M, X]
    exact fw_first_band_future_stock_budget bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last 10 S stages trace
      (by omega)
  obtain ⟨final, Rfinal, lastFinal, extra, htrace, hlen', hsub', hcard', hstop,
    hnarrow, hRfinal, heven', hbelow', hsched'⟩ :=
    fw_mixed_affine_iterate_bounded (4 : Fin 8) 10 trace 23 M M (3981035 / 10000000)
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

/-- After the supplied 118-, 6-, 11-, 12-, and 9-stage schedules,
start wheel 4 with a freshly checked origin. The continuation stops at
actual crossing or after ten further stages. -/
theorem fw_fifth_affine_phase_after_fourth
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (R₀ last₀ R₁ last₁ R₂ last₂ R₃ last₃ R₄ last₄ : ℕ) (S : Finset ℕ) (window first second third fourth : List BTSelectedStage)
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
    (hthird : FWMixedAffineCertifiedSchedule 2 n 23
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      (3981035 / 10000000) R₂ last₂ R₃ last₃ third)
    (hthirdlen : third.length = 12)
    (hfourth : FWMixedAffineCertifiedSchedule 3 n 23
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      (3981035 / 10000000) R₃ last₃ R₄ last₄ fourth)
    (hfourthlen : fourth.length = 9)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 S last₄ ((((window ++ first) ++ second) ++ third) ++ fourth)) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    ∃ (final : Finset ℕ) (Rfinal lastFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final lastFinal (((((window ++ first) ++ second) ++ third) ++ fourth) ++ extra) ∧
      extra.length ≤ 10 ∧ final ⊆ S ∧ final.card + 2 * Q * extra.length = S.card ∧
      (X / 23 ≤ lastFinal ∨ extra.length = 10) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages (X / 6) extra ∧
      R₄ ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ lastFinal ∧
      FWMixedAffineCertifiedSchedule 4 n 23 M M eta R₄ last₄ Rfinal lastFinal extra := by
  obtain ⟨hR, heven, hbelow, _horigin⟩ :=
    fw_fifth_entry_radius hwindow hwindowlen hfirst hfirstlen hsecond hsecondlen hthird hthirdlen hfourth
  have hlen : ((((window ++ first) ++ second) ++ third) ++ fourth).length ≤ 156 := by
    simp [hwindowlen, hfirstlen, hsecondlen, hthirdlen, hfourthlen]
  exact fw_fifth_affine_phase_from_156 bmor lower upper upperSharp hnlo hnhi
    batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R₄ last₄ S
    ((((window ++ first) ++ second) ++ third) ++ fourth) trace hlen hR heven hbelow

end
end Sude
