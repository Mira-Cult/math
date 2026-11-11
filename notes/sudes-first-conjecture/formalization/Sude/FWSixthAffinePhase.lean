import Sude.FWFifthAffinePhase

namespace Sude
noncomputable section

/-- For the sixth mixed wheel, the fixed conservative mass yields an
origin strictly below 34942. The input mf is normalized and multiplied by X. -/
theorem fw_sixth_affine_origin_lt_34942 {X mf : ℝ}
    (hX : 0 < X) (hmf : (3257 / 100000 : ℝ) ≤ mf) :
    fwAffineOrigin (fwMixedWheelError 5) 1 X (3981035 / 10000000) (mf * X) < 34942 := by
  have hmfpos : 0 < mf := by linarith
  have heq : fwAffineOrigin (fwMixedWheelError 5) 1 X (3981035 / 10000000) (mf * X) =
      (1 / 2 + fwMixedWheelError 5) / ((3981035 / 10000000) * mf) := by
    unfold fwAffineOrigin
    field_simp
  rw [heq]
  apply (div_lt_iff₀ (show 0 < (3981035 / 10000000 : ℝ) * mf by positivity)).2
  rw [show fwMixedWheelError 5 = (3025505777792 / 6685349671 : ℝ) by rfl]
  norm_num
  nlinarith

/-- The sixth mixed-wheel slope gate follows from the first-band mass
upper bound, for any positive X. -/
theorem fw_sixth_affine_slope_le_one {X m : ℝ}
    (hX : 0 < X) (hm : m ≤ (403 / 10000 : ℝ)) :
    fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 5 ≤ 1 := by
  have heq : fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 5 =
      (3981035 / 10000000 : ℝ) * 2 * m / fwMixedWheelRho 5 := by
    unfold fwAffineSlope
    field_simp
  rw [heq]
  rw [show fwMixedWheelRho 5 = (955514880 / 3212440751 : ℝ) by rfl]
  norm_num
  linarith

/-- On the sixth source wheel, continue the supplied trace up to ten
additional stages, preserving the actual crossing-or-fuel alternative. -/
theorem fw_sixth_affine_phase_from_166
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
    (hlen : stages.length ≤ 166) (hR : 34942 ≤ R) (heven : 2 ∣ R) (hbelow : R ≤ last) :
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
      FWMixedAffineCertifiedSchedule 5 n 23 M M eta R last Rfinal lastFinal extra := by
  dsimp only
  let X : ℝ := poolMaximum n
  let M : ℝ := (3257 / 100000 : ℝ) * X
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hM : 0 < M := by dsimp [M]; positivity
  have hRpos : 0 < R := by omega
  have horigin := fw_sixth_affine_origin_lt_34942 (X := X) (mf := (3257 / 100000 : ℝ)) hX (by norm_num)
  have hshift : 0 < (R : ℝ) - fwAffineOrigin (fwMixedWheelError 5) 1 X
      (3981035 / 10000000) M := by
    have hRreal : (34942 : ℝ) ≤ R := by exact_mod_cast hR
    dsimp [M]
    linarith
  have hslope : fwAffineSlope (3981035 / 10000000) 2 M 1 X / fwMixedWheelRho 5 ≤ 1 := by
    dsimp [M]
    exact fw_sixth_affine_slope_le_one hX (by norm_num)
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
    fw_mixed_affine_iterate_bounded (5 : Fin 8) 10 trace 23 M M (3981035 / 10000000)
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

/-- Fourth-wheel per-stage gain at radius 26985. -/
theorem fw_fourth_threshold_at_26985 (n : ℕ) :
    (1497 : ℝ) ≤ fwAffineThreshold 2 (fwMixedWheelRho 3)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) 26985 1
      (poolMaximum n) (fwMixedWheelError 3) := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have heq : fwAffineThreshold 2 (fwMixedWheelRho 3)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) 26985 1
      (poolMaximum n) (fwMixedWheelError 3) =
      2 / fwMixedWheelRho 3 * ((3981035 / 10000000 : ℝ) * (3257 / 100000) * 26985 -
        (1 / 2 + fwMixedWheelError 3)) := by
    unfold fwAffineThreshold
    field_simp
  rw [heq]
  norm_num [fwMixedWheelRho, fwMixedWheelError, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

/-- Nine fourth-wheel stages maintain a minimum aggregate gain. -/
theorem fw_fourth_nine_radius {n R actual Rfinal actualFinal : ℕ}
    {stages : List BTSelectedStage}
    (sched : FWMixedAffineCertifiedSchedule 3 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n)
      ((3257 / 100000 : ℝ) * poolMaximum n) (3981035 / 10000000)
      R actual Rfinal actualFinal stages)
    (hR : 26985 ≤ R) (hlen : stages.length = 9) : 40458 ≤ Rfinal := by
  have hM : (0 : ℝ) ≤ (3257 / 100000 : ℝ) * poolMaximum n := by positivity
  have hg := fw_affine_schedule_linear_growth_from_floor (k := 1497) (Rmin := 26985)
    sched hR (by norm_num) hM (fw_fourth_threshold_at_26985 n)
  rw [hlen] at hg
  omega

/-- The source-supplied schedules yield the next certified entry gate. -/
theorem fw_sixth_entry_radius {n : ℕ} {R₀ last₀ R₁ last₁ R₂ last₂ R₃ last₃ R₄ last₄ R₅ last₅ : ℕ}
    {window first second third fourth fifth : List BTSelectedStage}
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
      (3981035 / 10000000) R₃ last₃ R₄ last₄ fourth)
    (hfourthlen : fourth.length = 9)
    (hfifth : FWMixedAffineCertifiedSchedule 4 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n) ((3257 / 100000 : ℝ) * poolMaximum n)
      (3981035 / 10000000) R₄ last₄ R₅ last₅ fifth) :
    40458 ≤ R₅ ∧ 2 ∣ R₅ ∧ R₅ ≤ last₅ ∧
      fwAffineOrigin (fwMixedWheelError 5) 1 (poolMaximum n) (3981035 / 10000000)
        ((3257 / 100000 : ℝ) * poolMaximum n) < R₅ := by
  have hR₀ := fw_certified_118_radius_at_least_7118 hwindow hlen
  have hR₁ := fw_six_first_affine_stages_radius_9710 hfirst hR₀ hfirstlen
  have hR₂ := fw_second_eleven_radius hsecond hR₁ hsecondlen
  have hR₃ := fw_third_twelve_radius hthird hR₂ hthirdlen
  have hR₄ := fw_fourth_nine_radius hfourth hR₃ hfourthlen
  have hR₅ := hR₄.trans (affine_schedule_radius_le hfifth)
  obtain ⟨heven, hbelow⟩ := fw_certified_schedule_endpoint_from_32 hwindow (by decide)
  obtain ⟨heven₁, hbelow₁⟩ := fw_mixed_affine_schedule_endpoint hfirst heven hbelow
  obtain ⟨heven₂, hbelow₂⟩ := fw_mixed_affine_schedule_endpoint hsecond heven₁ hbelow₁
  obtain ⟨heven₃, hbelow₃⟩ := fw_mixed_affine_schedule_endpoint hthird heven₂ hbelow₂
  obtain ⟨heven₄, hbelow₄⟩ := fw_mixed_affine_schedule_endpoint hfourth heven₃ hbelow₃
  obtain ⟨heven₅, hbelow₅⟩ := fw_mixed_affine_schedule_endpoint hfifth heven₄ hbelow₄
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have horigin := fw_sixth_affine_origin_lt_34942 (X := poolMaximum n)
    (mf := (3257 / 100000 : ℝ)) hX (by norm_num)
  have hR₅real : (40458 : ℝ) ≤ R₅ := by exact_mod_cast hR₅
  exact ⟨hR₅, heven₅, hbelow₅, by linarith⟩

/-- After the supplied 118-, 6-, 11-, 12-, 9-, and 10-stage schedules,
start wheel 5 with a freshly checked origin. The continuation stops at
actual crossing or after ten further stages. -/
theorem fw_sixth_affine_phase_after_fifth
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (R₀ last₀ R₁ last₁ R₂ last₂ R₃ last₃ R₄ last₄ R₅ last₅ : ℕ) (S : Finset ℕ) (window first second third fourth fifth : List BTSelectedStage)
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
    (hfifth : FWMixedAffineCertifiedSchedule 4 n 23
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      (3981035 / 10000000) R₄ last₄ R₅ last₅ fifth)
    (hfifthlen : fifth.length = 10)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 S last₅ (((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth)) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    ∃ (final : Finset ℕ) (Rfinal lastFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final lastFinal ((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ extra) ∧
      extra.length ≤ 10 ∧ final ⊆ S ∧ final.card + 2 * Q * extra.length = S.card ∧
      (X / 23 ≤ lastFinal ∨ extra.length = 10) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages (X / 6) extra ∧
      R₅ ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ lastFinal ∧
      FWMixedAffineCertifiedSchedule 5 n 23 M M eta R₅ last₅ Rfinal lastFinal extra := by
  obtain ⟨hR, heven, hbelow, _horigin⟩ :=
    fw_sixth_entry_radius hwindow hwindowlen hfirst hfirstlen hsecond hsecondlen hthird hthirdlen hfourth hfourthlen hfifth
  have hRweak : 34942 ≤ R₅ := by omega
  have hlen : (((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth).length ≤ 166 := by
    simp [hwindowlen, hfirstlen, hsecondlen, hthirdlen, hfourthlen, hfifthlen]
  exact fw_sixth_affine_phase_from_166 bmor lower upper upperSharp hnlo hnhi
    batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R₅ last₅ S
    (((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) trace hlen hRweak heven hbelow

end
end Sude
