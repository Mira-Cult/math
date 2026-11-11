import Sude.FWThirdAffinePhase

namespace Sude
noncomputable section

/-- If the real source threshold is at least k for every certified radius
above Rmin, every stage increases the certified radius by at least k. -/
theorem fw_affine_schedule_linear_growth
    {i : Fin 8} {n k Rmin : ℕ} {L M Mf eta : ℝ}
    {R actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWMixedAffineCertifiedSchedule i n L M Mf eta R actual Rfinal actualFinal stages)
    (hstart : Rmin ≤ R)
    (hbound : ∀ r : ℕ, Rmin ≤ r → (k : ℝ) ≤
      fwAffineThreshold 2 (fwMixedWheelRho i) eta M r 1 (poolMaximum n)
        (fwMixedWheelError i)) :
    R + stages.length * k ≤ Rfinal := by
  induction sched with
  | nil R actual => simp
  | cons R actual Rfinal actualFinal stage tail hbefore hbelow hshift hminimum
      hpositive hgapEven hlower hupper hrest ih =>
    have hkreal := (hbound R hstart).trans
      (fw_mixed_affine_threshold_le_increment i n R M eta)
    have hk : k ≤ fwMixedAffineEvenIncrement i n R M eta := by exact_mod_cast hkreal
    have hnext : Rmin ≤ R + fwMixedAffineEvenIncrement i n R M eta := by omega
    have hrest' := ih hnext
    simp only [List.length_cons, Nat.succ_mul] at *
    omega

/-- It suffices to verify a threshold lower bound at the initial floor,
because the affine threshold is nondecreasing in its radius. -/
theorem fw_affine_schedule_linear_growth_from_floor
    {i : Fin 8} {n k Rmin : ℕ} {L M Mf eta : ℝ}
    {R actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWMixedAffineCertifiedSchedule i n L M Mf eta R actual Rfinal actualFinal stages)
    (hstart : Rmin ≤ R) (heta : 0 ≤ eta) (hM : 0 ≤ M)
    (hbound : (k : ℝ) ≤ fwAffineThreshold 2 (fwMixedWheelRho i) eta M Rmin 1
      (poolMaximum n) (fwMixedWheelError i)) :
    R + stages.length * k ≤ Rfinal := by
  apply fw_affine_schedule_linear_growth sched hstart
  intro r hr
  have hr' : (Rmin : ℝ) ≤ r := by exact_mod_cast hr
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hm := fw_affine_threshold_mono_radius (g := 2) (rho := fwMixedWheelRho i)
    (eta := eta) (M := M) (r := 1) (X := poolMaximum n) (C := fwMixedWheelError i)
    (by norm_num) (fw_mixed_wheel_rho_pos i) heta hM (by norm_num) hX hr'
  exact hbound.trans hm

/-- At certified radius 7118, the first wheel's conservative threshold
is at least 432, for any positive actual pool maximum. -/
theorem fw_first_affine_threshold_at_7118 (n : ℕ) :
    (432 : ℝ) ≤ fwAffineThreshold 2 (fwMixedWheelRho 0)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) 7118 1
      (poolMaximum n) (fwMixedWheelError 0) := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have heq : fwAffineThreshold 2 (fwMixedWheelRho 0)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) 7118 1
      (poolMaximum n) (fwMixedWheelError 0) =
      2 / fwMixedWheelRho 0 * ((3981035 / 10000000 : ℝ) * (3257 / 100000) * 7118 -
        (1 / 2 + fwMixedWheelError 0)) := by
    unfold fwAffineThreshold
    field_simp
  rw [heq]
  norm_num [fwMixedWheelRho, fwMixedWheelError]

/-- Six supplied first-wheel stages lift a certified radius of at least
7118 to at least 9710, without a crossing assertion. -/
theorem fw_six_first_affine_stages_radius_9710 {n R actual Rfinal actualFinal : ℕ}
    {stages : List BTSelectedStage}
    (sched : FWMixedAffineCertifiedSchedule 0 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n)
      ((3257 / 100000 : ℝ) * poolMaximum n) (3981035 / 10000000)
      R actual Rfinal actualFinal stages)
    (hR : 7118 ≤ R) (hlen : stages.length = 6) : 9710 ≤ Rfinal := by
  have hM : (0 : ℝ) ≤ (3257 / 100000 : ℝ) * poolMaximum n := by positivity
  have hg := fw_affine_schedule_linear_growth_from_floor (k := 432) (Rmin := 7118)
    sched hR (by norm_num) hM (fw_first_affine_threshold_at_7118 n)
  rw [hlen] at hg
  omega

/-- For the fourth mixed wheel, the fixed conservative mass yields an
origin strictly below 8747. The input mf is normalized and multiplied by X. -/
theorem fw_fourth_affine_origin_lt_8747 {X mf : ℝ}
    (hX : 0 < X) (hmf : (3257 / 100000 : ℝ) ≤ mf) :
    fwAffineOrigin (fwMixedWheelError 3) 1 X (3981035 / 10000000) (mf * X) < 8747 := by
  have hmfpos : 0 < mf := by linarith
  have heq : fwAffineOrigin (fwMixedWheelError 3) 1 X (3981035 / 10000000) (mf * X) =
      (1 / 2 + fwMixedWheelError 3) / ((3981035 / 10000000) * mf) := by
    unfold fwAffineOrigin
    field_simp
  rw [heq]
  apply (div_lt_iff₀ (show 0 < (3981035 / 10000000 : ℝ) * mf by positivity)).2
  norm_num [fwMixedWheelError, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  nlinarith

/-- Supplied completed six-stage first phase and any two following certified
schedules suffice to clear the origin of the next wheel. -/
theorem fw_fourth_affine_entry_radius {n : ℕ} {R₀ last₀ R₁ last₁ R₂ last₂ R₃ last₃ : ℕ}
    {window first second third : List BTSelectedStage}
    (hwindow : FWFirstWindowCertifiedSchedule (poolMaximum n) 0 32 32 R₀ last₀ window)
    (hlen : window.length = 118)
    (hfirst : FWMixedAffineCertifiedSchedule 0 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n) ((3257 / 100000 : ℝ) * poolMaximum n)
      (3981035 / 10000000) R₀ last₀ R₁ last₁ first)
    (hfirstlen : first.length = 6)
    (hsecond : FWMixedAffineCertifiedSchedule 1 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n) ((3257 / 100000 : ℝ) * poolMaximum n)
      (3981035 / 10000000) R₁ last₁ R₂ last₂ second)
    (hthird : FWMixedAffineCertifiedSchedule 2 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n) ((3257 / 100000 : ℝ) * poolMaximum n)
      (3981035 / 10000000) R₂ last₂ R₃ last₃ third) :
    9710 ≤ R₃ ∧ 2 ∣ R₃ ∧ R₃ ≤ last₃ ∧
      fwAffineOrigin (fwMixedWheelError 3) 1 (poolMaximum n) (3981035 / 10000000)
        ((3257 / 100000 : ℝ) * poolMaximum n) < R₃ := by
  have hR₀ := fw_certified_118_radius_at_least_7118 hwindow hlen
  have hR₁ := fw_six_first_affine_stages_radius_9710 hfirst hR₀ hfirstlen
  have hR₂ := hR₁.trans (affine_schedule_radius_le hsecond)
  have hR₃ := hR₂.trans (affine_schedule_radius_le hthird)
  obtain ⟨heven, hbelow⟩ := fw_certified_schedule_endpoint_from_32 hwindow (by decide)
  obtain ⟨heven₁, hbelow₁⟩ := fw_mixed_affine_schedule_endpoint hfirst heven hbelow
  obtain ⟨heven₂, hbelow₂⟩ := fw_mixed_affine_schedule_endpoint hsecond heven₁ hbelow₁
  obtain ⟨heven₃, hbelow₃⟩ := fw_mixed_affine_schedule_endpoint hthird heven₂ hbelow₂
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have horigin := fw_fourth_affine_origin_lt_8747 (X := poolMaximum n)
    (mf := (3257 / 100000 : ℝ)) hX (by norm_num)
  have hR₃real : (9710 : ℝ) ≤ R₃ := by exact_mod_cast hR₃
  exact ⟨hR₃, heven₃, hbelow₃, by linarith⟩

/-- The fourth mixed-wheel slope gate follows from the first-band mass
upper bound, for any positive X. -/
theorem fw_fourth_affine_slope_le_one {X m : ℝ}
    (hX : 0 < X) (hm : m ≤ (403 / 10000 : ℝ)) :
    fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 3 ≤ 1 := by
  have heq : fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 3 =
      (3981035 / 10000000 : ℝ) * 2 * m / fwMixedWheelRho 3 := by
    unfold fwAffineSlope
    field_simp
  rw [heq]
  norm_num [fwMixedWheelRho, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  linarith



/-- On the fourth source wheel, continue the supplied trace up to nine
additional stages, preserving the actual crossing-or-fuel alternative. -/
theorem fw_fourth_affine_phase_from_147
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
    (hlen : stages.length ≤ 147) (hR : 9710 ≤ R) (heven : 2 ∣ R) (hbelow : R ≤ last) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    ∃ (final : Finset ℕ) (Rfinal lastFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final lastFinal (stages ++ extra) ∧
      extra.length ≤ 9 ∧ final ⊆ S ∧ final.card + 2 * Q * extra.length = S.card ∧
      (X / 23 ≤ lastFinal ∨ extra.length = 9) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages (X / 6) extra ∧
      R ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ lastFinal ∧
      FWMixedAffineCertifiedSchedule 3 n 23 M M eta R last Rfinal lastFinal extra := by
  dsimp only
  let X : ℝ := poolMaximum n
  let M : ℝ := (3257 / 100000 : ℝ) * X
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hM : 0 < M := by dsimp [M]; positivity
  have hRpos : 0 < R := by omega
  have horigin := fw_fourth_affine_origin_lt_8747 (X := X) (mf := (3257 / 100000 : ℝ)) hX (by norm_num)
  have hshift : 0 < (R : ℝ) - fwAffineOrigin (fwMixedWheelError 3) 1 X
      (3981035 / 10000000) M := by
    have hRreal : (9710 : ℝ) ≤ R := by exact_mod_cast hR
    dsimp [M]
    linarith
  have hslope : fwAffineSlope (3981035 / 10000000) 2 M 1 X / fwMixedWheelRho 3 ≤ 1 := by
    dsimp [M]
    exact fw_fourth_affine_slope_le_one hX (by norm_num)
  have hscreen : S ⊆ (poolFinset n).filter (fun p => 43 < p) :=
    trace.final_accounting.1.trans Finset.sdiff_subset
  have hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) * X ≤
      (1 / (2 * (1 + 1 / (23 : ℝ))) - 3981035 / 10000000) * M ^ 2 := by
    dsimp [M, X]
    convert fw_first_affine_absolute_quota bmor lower upper upperSharp hnlo hnhi using 1; norm_num
  have hbudget : M + ((2 * (6 * (n + 8)) * 9 : ℕ) : ℝ) ≤ S.card := by
    dsimp [M, X]
    exact fw_first_band_future_stock_budget bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last 9 S stages trace
      (by omega)
  obtain ⟨final, Rfinal, lastFinal, extra, htrace, hlen', hsub', hcard', hstop,
    hnarrow, hRfinal, heven', hbelow', hsched'⟩ :=
    fw_mixed_affine_iterate_bounded (3 : Fin 8) 9 trace 23 M M (3981035 / 10000000)
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






/-- After a supplied complete certified 118-stage window schedule, six first-wheel stages, eleven second-wheel stages, and twelve third-wheel
stages, start wheel 3 with a freshly checked origin. It stops at actual
crossing or after nine further stages. -/
theorem fw_fourth_affine_phase_after_third
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (R₀ last₀ R₁ last₁ R₂ last₂ R₃ last₃ : ℕ) (S : Finset ℕ) (window first second third : List BTSelectedStage)
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
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 S last₃ (((window ++ first) ++ second) ++ third)) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    ∃ (final : Finset ℕ) (Rfinal lastFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final lastFinal ((((window ++ first) ++ second) ++ third) ++ extra) ∧
      extra.length ≤ 9 ∧ final ⊆ S ∧ final.card + 2 * Q * extra.length = S.card ∧
      (X / 23 ≤ lastFinal ∨ extra.length = 9) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages (X / 6) extra ∧
      R₃ ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ lastFinal ∧
      FWMixedAffineCertifiedSchedule 3 n 23 M M eta R₃ last₃ Rfinal lastFinal extra := by
  obtain ⟨hR, heven, hbelow, _horigin⟩ :=
    fw_fourth_affine_entry_radius hwindow hwindowlen hfirst hfirstlen hsecond hthird
  have hlen : (((window ++ first) ++ second) ++ third).length ≤ 147 := by
    simp [hwindowlen, hfirstlen, hsecondlen, hthirdlen]
  exact fw_fourth_affine_phase_from_147 bmor lower upper upperSharp hnlo hnhi
    batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R₃ last₃ S
    (((window ++ first) ++ second) ++ third) trace hlen hR heven hbelow


end
end Sude
