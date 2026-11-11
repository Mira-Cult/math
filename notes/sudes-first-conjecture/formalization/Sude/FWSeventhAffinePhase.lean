import Sude.FWSixthAffinePhase

namespace Sude
noncomputable section

/-- For the seventh mixed wheel, the fixed conservative mass yields an
origin strictly below 69868. The input mf is normalized and multiplied by X. -/
theorem fw_seventh_affine_origin_lt_69868 {X mf : ℝ}
    (hX : 0 < X) (hmf : (3257 / 100000 : ℝ) ≤ mf) :
    fwAffineOrigin (fwMixedWheelError 6) 1 X (3981035 / 10000000) (mf * X) < 69868 := by
  have hmfpos : 0 < mf := by linarith
  have heq : fwAffineOrigin (fwMixedWheelError 6) 1 X (3981035 / 10000000) (mf * X) =
      (1 / 2 + fwMixedWheelError 6) / ((3981035 / 10000000) * mf) := by
    unfold fwAffineOrigin
    field_simp
  rw [heq]
  apply (div_lt_iff₀ (show 0 < (3981035 / 10000000 : ℝ) * mf by positivity)).2
  rw [show fwMixedWheelError 6 = (7722793179392 / 8529584063 : ℝ) by rfl]
  norm_num
  nlinarith

/-- The seventh mixed-wheel slope gate follows from the first-band mass
upper bound, for any positive X. -/
theorem fw_seventh_affine_slope_le_one {X m : ℝ}
    (hX : 0 < X) (hm : m ≤ (403 / 10000 : ℝ)) :
    fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 6 ≤ 1 := by
  have heq : fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 6 =
      (3981035 / 10000000 : ℝ) * 2 * m / fwMixedWheelRho 6 := by
    unfold fwAffineSlope
    field_simp
  rw [heq]
  rw [show fwMixedWheelRho 6 = (38220595200 / 131710070791 : ℝ) by rfl]
  norm_num
  linarith

/-- On the seventh source wheel, continue the supplied trace up to eight
additional stages, preserving the actual crossing-or-fuel alternative. -/
theorem fw_seventh_affine_phase_from_176
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
    (hlen : stages.length ≤ 176) (hR : 69868 ≤ R) (heven : 2 ∣ R) (hbelow : R ≤ last) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    ∃ (final : Finset ℕ) (Rfinal lastFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final lastFinal (stages ++ extra) ∧
      extra.length ≤ 8 ∧ final ⊆ S ∧ final.card + 2 * Q * extra.length = S.card ∧
      (X / 23 ≤ lastFinal ∨ extra.length = 8) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages (X / 6) extra ∧
      R ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ lastFinal ∧
      FWMixedAffineCertifiedSchedule 6 n 23 M M eta R last Rfinal lastFinal extra := by
  dsimp only
  let X : ℝ := poolMaximum n
  let M : ℝ := (3257 / 100000 : ℝ) * X
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hM : 0 < M := by dsimp [M]; positivity
  have hRpos : 0 < R := by omega
  have horigin := fw_seventh_affine_origin_lt_69868 (X := X) (mf := (3257 / 100000 : ℝ)) hX (by norm_num)
  have hshift : 0 < (R : ℝ) - fwAffineOrigin (fwMixedWheelError 6) 1 X
      (3981035 / 10000000) M := by
    have hRreal : (69868 : ℝ) ≤ R := by exact_mod_cast hR
    dsimp [M]
    linarith
  have hslope : fwAffineSlope (3981035 / 10000000) 2 M 1 X / fwMixedWheelRho 6 ≤ 1 := by
    dsimp [M]
    exact fw_seventh_affine_slope_le_one hX (by norm_num)
  have hscreen : S ⊆ (poolFinset n).filter (fun p => 43 < p) :=
    trace.final_accounting.1.trans Finset.sdiff_subset
  have hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) * X ≤
      (1 / (2 * (1 + 1 / (23 : ℝ))) - 3981035 / 10000000) * M ^ 2 := by
    dsimp [M, X]
    convert fw_first_affine_absolute_quota bmor lower upper upperSharp hnlo hnhi using 1; norm_num
  have hbudget : M + ((2 * (6 * (n + 8)) * 8 : ℕ) : ℝ) ≤ S.card := by
    dsimp [M, X]
    exact fw_first_band_future_stock_budget bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last 8 S stages trace
      (by omega)
  obtain ⟨final, Rfinal, lastFinal, extra, htrace, hlen', hsub', hcard', hstop,
    hnarrow, hRfinal, heven', hbelow', hsched'⟩ :=
    fw_mixed_affine_iterate_bounded (6 : Fin 8) 8 trace 23 M M (3981035 / 10000000)
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

/-- Per-stage threshold on index 4 at certified radius 40458. -/
theorem fw_fifth_threshold_at_40458 (n : ℕ) :
    (1949 : ℝ) ≤ fwAffineThreshold 2 (fwMixedWheelRho 4)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) 40458 1
      (poolMaximum n) (fwMixedWheelError 4) := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have heq : fwAffineThreshold 2 (fwMixedWheelRho 4)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) 40458 1
      (poolMaximum n) (fwMixedWheelError 4) =
      2 / fwMixedWheelRho 4 * ((3981035 / 10000000 : ℝ) * (3257 / 100000) * 40458 -
        (1 / 2 + fwMixedWheelError 4)) := by
    unfold fwAffineThreshold
    field_simp
  rw [heq]
  rw [show fwMixedWheelRho 4 = (26542080 / 86822723 : ℝ) by rfl,
      show fwMixedWheelError 4 = (150976832 / 667667 : ℝ) by rfl]
  norm_num

/-- Per-stage threshold on index 5 at certified radius 59948. -/
theorem fw_sixth_threshold_at_59948 (n : ℕ) :
    (2179 : ℝ) ≤ fwAffineThreshold 2 (fwMixedWheelRho 5)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) 59948 1
      (poolMaximum n) (fwMixedWheelError 5) := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have heq : fwAffineThreshold 2 (fwMixedWheelRho 5)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) 59948 1
      (poolMaximum n) (fwMixedWheelError 5) =
      2 / fwMixedWheelRho 5 * ((3981035 / 10000000 : ℝ) * (3257 / 100000) * 59948 -
        (1 / 2 + fwMixedWheelError 5)) := by
    unfold fwAffineThreshold
    field_simp
  rw [heq]
  rw [show fwMixedWheelRho 5 = (955514880 / 3212440751 : ℝ) by rfl,
      show fwMixedWheelError 5 = (3025505777792 / 6685349671 : ℝ) by rfl]
  norm_num

theorem fw_fifth_ten_radius {n R actual Rfinal actualFinal : ℕ}
    {stages : List BTSelectedStage}
    (sched : FWMixedAffineCertifiedSchedule 4 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n)
      ((3257 / 100000 : ℝ) * poolMaximum n) (3981035 / 10000000)
      R actual Rfinal actualFinal stages)
    (hR : 40458 ≤ R) (hlen : stages.length = 10) : 59948 ≤ Rfinal := by
  have hM : (0 : ℝ) ≤ (3257 / 100000 : ℝ) * poolMaximum n := by positivity
  have hg := fw_affine_schedule_linear_growth_from_floor (k := 1949) (Rmin := 40458)
    sched hR (by norm_num) hM (fw_fifth_threshold_at_40458 n)
  rw [hlen] at hg
  omega

theorem fw_sixth_ten_radius {n R actual Rfinal actualFinal : ℕ}
    {stages : List BTSelectedStage}
    (sched : FWMixedAffineCertifiedSchedule 5 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n)
      ((3257 / 100000 : ℝ) * poolMaximum n) (3981035 / 10000000)
      R actual Rfinal actualFinal stages)
    (hR : 59948 ≤ R) (hlen : stages.length = 10) : 81738 ≤ Rfinal := by
  have hM : (0 : ℝ) ≤ (3257 / 100000 : ℝ) * poolMaximum n := by positivity
  have hg := fw_affine_schedule_linear_growth_from_floor (k := 2179) (Rmin := 59948)
    sched hR (by norm_num) hM (fw_sixth_threshold_at_59948 n)
  rw [hlen] at hg
  omega

theorem fw_seventh_entry_radius {n : ℕ} {R₀ last₀ R₁ last₁ R₂ last₂ R₃ last₃ R₄ last₄ R₅ last₅ R₆ last₆ : ℕ}
    {window first second third fourth fifth sixth : List BTSelectedStage}
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
      (3981035 / 10000000) R₄ last₄ R₅ last₅ fifth)
    (hfifthlen : fifth.length = 10)
    (hsixth : FWMixedAffineCertifiedSchedule 5 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n) ((3257 / 100000 : ℝ) * poolMaximum n)
      (3981035 / 10000000) R₅ last₅ R₆ last₆ sixth)
    (hsixthlen : sixth.length = 10) :
    81738 ≤ R₆ ∧ 2 ∣ R₆ ∧ R₆ ≤ last₆ ∧
      fwAffineOrigin (fwMixedWheelError 6) 1 (poolMaximum n) (3981035 / 10000000)
        ((3257 / 100000 : ℝ) * poolMaximum n) < R₆ := by
  have hR₀ := fw_certified_118_radius_at_least_7118 hwindow hlen
  have hR₁ := fw_six_first_affine_stages_radius_9710 hfirst hR₀ hfirstlen
  have hR₂ := fw_second_eleven_radius hsecond hR₁ hsecondlen
  have hR₃ := fw_third_twelve_radius hthird hR₂ hthirdlen
  have hR₄ := fw_fourth_nine_radius hfourth hR₃ hfourthlen
  have hR₅ := fw_fifth_ten_radius hfifth hR₄ hfifthlen
  have hR₆ := fw_sixth_ten_radius hsixth hR₅ hsixthlen
  obtain ⟨heven, hbelow⟩ := fw_certified_schedule_endpoint_from_32 hwindow (by decide)
  obtain ⟨heven₁, hbelow₁⟩ := fw_mixed_affine_schedule_endpoint hfirst heven hbelow
  obtain ⟨heven₂, hbelow₂⟩ := fw_mixed_affine_schedule_endpoint hsecond heven₁ hbelow₁
  obtain ⟨heven₃, hbelow₃⟩ := fw_mixed_affine_schedule_endpoint hthird heven₂ hbelow₂
  obtain ⟨heven₄, hbelow₄⟩ := fw_mixed_affine_schedule_endpoint hfourth heven₃ hbelow₃
  obtain ⟨heven₅, hbelow₅⟩ := fw_mixed_affine_schedule_endpoint hfifth heven₄ hbelow₄
  obtain ⟨heven₆, hbelow₆⟩ := fw_mixed_affine_schedule_endpoint hsixth heven₅ hbelow₅
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have horigin := fw_seventh_affine_origin_lt_69868 (X := poolMaximum n)
    (mf := (3257 / 100000 : ℝ)) hX (by norm_num)
  have hR₆real : (81738 : ℝ) ≤ R₆ := by exact_mod_cast hR₆
  exact ⟨hR₆, heven₆, hbelow₆, by linarith⟩

/-- After the supplied 118-, 6-, 11-, 12-, 9-, 10-, and 10-stage schedules,
start wheel 6 with a freshly checked origin. The continuation stops at
actual crossing or after eight further stages. -/
theorem fw_seventh_affine_phase_after_sixth
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (R₀ last₀ R₁ last₁ R₂ last₂ R₃ last₃ R₄ last₄ R₅ last₅ R₆ last₆ : ℕ) (S : Finset ℕ) (window first second third fourth fifth sixth : List BTSelectedStage)
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
    (hsixth : FWMixedAffineCertifiedSchedule 5 n 23
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      (3981035 / 10000000) R₅ last₅ R₆ last₆ sixth)
    (hsixthlen : sixth.length = 10)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 S last₆ ((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth)) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    ∃ (final : Finset ℕ) (Rfinal lastFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final lastFinal (((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth) ++ extra) ∧
      extra.length ≤ 8 ∧ final ⊆ S ∧ final.card + 2 * Q * extra.length = S.card ∧
      (X / 23 ≤ lastFinal ∨ extra.length = 8) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages (X / 6) extra ∧
      R₆ ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ lastFinal ∧
      FWMixedAffineCertifiedSchedule 6 n 23 M M eta R₆ last₆ Rfinal lastFinal extra := by
  obtain ⟨hR, heven, hbelow, _horigin⟩ :=
    fw_seventh_entry_radius hwindow hwindowlen hfirst hfirstlen hsecond hsecondlen hthird hthirdlen hfourth hfourthlen hfifth hfifthlen hsixth hsixthlen
  have hRweak : 69868 ≤ R₆ := by omega
  have hlen : ((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth).length ≤ 176 := by
    simp [hwindowlen, hfirstlen, hsecondlen, hthirdlen, hfourthlen, hfifthlen, hsixthlen]
  exact fw_seventh_affine_phase_from_176 bmor lower upper upperSharp hnlo hnhi
    batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R₆ last₆ S
    ((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth) trace hlen hRweak heven hbelow

end
end Sude
