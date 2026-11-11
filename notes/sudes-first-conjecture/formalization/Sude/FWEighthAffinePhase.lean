import Sude.FWSeventhAffinePhase

namespace Sude
noncomputable section

/-- For the eighth mixed wheel, the fixed conservative mass yields an
origin strictly below 139718. The input mf is normalized and multiplied by X. -/
theorem fw_eighth_affine_origin_lt_139718 {X mf : ℝ}
    (hX : 0 < X) (hmf : (3257 / 100000 : ℝ) ≤ mf) :
    fwAffineOrigin (fwMixedWheelError 7) 1 X (3981035 / 10000000) (mf * X) < 139718 := by
  have hmfpos : 0 < mf := by linarith
  have heq : fwAffineOrigin (fwMixedWheelError 7) 1 X (3981035 / 10000000) (mf * X) =
      (1 / 2 + fwMixedWheelError 7) / ((3981035 / 10000000) * mf) := by
    unfold fwAffineOrigin
    field_simp
  rw [heq]
  apply (div_lt_iff₀ (show 0 < (3981035 / 10000000 : ℝ) * mf by positivity)).2
  rw [show fwMixedWheelError 7 = (1412903474340352 / 780128880839 : ℝ) by rfl]
  norm_num
  nlinarith

/-- The eighth mixed-wheel slope gate follows from the first-band mass
upper bound, for any positive X. -/
theorem fw_eighth_affine_slope_le_one {X m : ℝ}
    (hX : 0 < X) (hm : m ≤ (403 / 10000 : ℝ)) :
    fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 7 ≤ 1 := by
  have heq : fwAffineSlope (3981035 / 10000000) 2 (m * X) 1 X / fwMixedWheelRho 7 =
      (3981035 / 10000000 : ℝ) * 2 * m / fwMixedWheelRho 7 := by
    unfold fwAffineSlope
    field_simp
  rw [heq]
  rw [show fwMixedWheelRho 7 = (1605264998400 / 5663533044013 : ℝ) by rfl]
  norm_num
  linarith

/-- On the eighth source wheel, continue the supplied trace up to forty-four
additional stages, preserving the actual crossing-or-fuel alternative. -/
theorem fw_eighth_affine_phase_from_184
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
    (hlen : stages.length ≤ 184) (hR : 139718 ≤ R) (heven : 2 ∣ R) (hbelow : R ≤ last) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    ∃ (final : Finset ℕ) (Rfinal lastFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final lastFinal (stages ++ extra) ∧
      extra.length ≤ 44 ∧ final ⊆ S ∧ final.card + 2 * Q * extra.length = S.card ∧
      (X / 23 ≤ lastFinal ∨ extra.length = 44) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages (X / 6) extra ∧
      R ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ lastFinal ∧
      FWMixedAffineCertifiedSchedule 7 n 23 M M eta R last Rfinal lastFinal extra := by
  dsimp only
  let X : ℝ := poolMaximum n
  let M : ℝ := (3257 / 100000 : ℝ) * X
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hM : 0 < M := by dsimp [M]; positivity
  have hRpos : 0 < R := by omega
  have horigin := fw_eighth_affine_origin_lt_139718 (X := X) (mf := (3257 / 100000 : ℝ)) hX (by norm_num)
  have hshift : 0 < (R : ℝ) - fwAffineOrigin (fwMixedWheelError 7) 1 X
      (3981035 / 10000000) M := by
    have hRreal : (139718 : ℝ) ≤ R := by exact_mod_cast hR
    dsimp [M]
    linarith
  have hslope : fwAffineSlope (3981035 / 10000000) 2 M 1 X / fwMixedWheelRho 7 ≤ 1 := by
    dsimp [M]
    exact fw_eighth_affine_slope_le_one hX (by norm_num)
  have hscreen : S ⊆ (poolFinset n).filter (fun p => 43 < p) :=
    trace.final_accounting.1.trans Finset.sdiff_subset
  have hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) * X ≤
      (1 / (2 * (1 + 1 / (23 : ℝ))) - 3981035 / 10000000) * M ^ 2 := by
    dsimp [M, X]
    convert fw_first_affine_absolute_quota bmor lower upper upperSharp hnlo hnhi using 1; norm_num
  have hbudget : M + ((2 * (6 * (n + 8)) * 44 : ℕ) : ℝ) ≤ S.card := by
    dsimp [M, X]
    exact fw_first_band_future_stock_budget bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last 44 S stages trace
      (by omega)
  obtain ⟨final, Rfinal, lastFinal, extra, htrace, hlen', hsub', hcard', hstop,
    hnarrow, hRfinal, heven', hbelow', hsched'⟩ :=
    fw_mixed_affine_iterate_bounded (7 : Fin 8) 44 trace 23 M M (3981035 / 10000000)
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

/-- Conservative per-stage radius growth, using natural-number floor division. -/
def fwLowerGrowth (d : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | n + 1, r => fwLowerGrowth d n (r + r / d)

/-- A certified schedule dominates any uniform lower-growth recurrence. -/
theorem fw_schedule_lower_growth
    {i : Fin 8} {n d : ℕ} {L M Mf eta : ℝ}
    {R actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWMixedAffineCertifiedSchedule i n L M Mf eta R actual Rfinal actualFinal stages) :
    ∀ floor : ℕ, floor ≤ R →
      (∀ r : ℕ, floor ≤ r → r / d ≤ fwMixedAffineEvenIncrement i n r M eta) →
      fwLowerGrowth d stages.length floor ≤ Rfinal := by
  induction sched with
  | nil R actual =>
      intro floor hfloor _
      simpa [fwLowerGrowth] using hfloor
  | cons R actual Rfinal actualFinal stage tail hbefore hbelow hshift hminimum
      hpositive hgapEven hlower hupper hrest ih =>
    intro floor hfloor hstep
    have hd : floor / d ≤ R / d := Nat.div_le_div_right hfloor
    have hi := hstep R hfloor
    have hn : floor + floor / d ≤ R + fwMixedAffineEvenIncrement i n R M eta := by omega
    have hs : ∀ r : ℕ, floor + floor / d ≤ r →
        r / d ≤ fwMixedAffineEvenIncrement i n r M eta := by
      intro r hr
      exact hstep r (le_trans (Nat.le_add_right floor _) hr)
    simpa [fwLowerGrowth] using ih (floor + floor / d) hn hs

theorem fw_increment_proportional {i : Fin 8} {n floor d : ℕ}
    (hd : 0 < d)
    (hbound : ∀ r : ℕ, floor ≤ r → ((r : ℝ) / d) ≤
      fwAffineThreshold 2 (fwMixedWheelRho i) (3981035 / 10000000)
        ((3257 / 100000 : ℝ) * poolMaximum n) r 1 (poolMaximum n) (fwMixedWheelError i)) :
    ∀ r : ℕ, floor ≤ r → r / d ≤ fwMixedAffineEvenIncrement i n r
      ((3257 / 100000 : ℝ) * poolMaximum n) (3981035 / 10000000) := by
  intro r hr
  have hdivnat := Nat.div_mul_le_self r d
  have hdivreal : ((r / d : ℕ) : ℝ) * d ≤ r := by exact_mod_cast hdivnat
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hdiv : ((r / d : ℕ) : ℝ) ≤ (r : ℝ) / d := (le_div_iff₀ hdreal).2 hdivreal
  have h := hdiv.trans ((hbound r hr).trans (fw_mixed_affine_threshold_le_increment i n r
    ((3257 / 100000 : ℝ) * poolMaximum n) (3981035 / 10000000)))
  exact_mod_cast h

theorem fw_prop_wheel0 (n : ℕ) : ∀ r : ℕ, 7118 ≤ r →
    (r : ℝ) / 20 ≤ fwAffineThreshold 2 (fwMixedWheelRho 0)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) r 1
      (poolMaximum n) (fwMixedWheelError 0) := by
  intro r hr
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hrreal : (7118 : ℝ) ≤ r := by exact_mod_cast hr
  have heq : fwAffineThreshold 2 (fwMixedWheelRho 0)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) r 1
      (poolMaximum n) (fwMixedWheelError 0) =
      2 / fwMixedWheelRho 0 * ((3981035 / 10000000 : ℝ) * (3257 / 100000) * r -
        (1 / 2 + fwMixedWheelError 0)) := by
    unfold fwAffineThreshold
    field_simp
  rw [heq]
  rw [show fwMixedWheelRho 0 = (6144 / 17017 : ℝ) by rfl,
      show fwMixedWheelError 0 = (13820 / 1001 : ℝ) by rfl]
  norm_num
  nlinarith

theorem fw_prop_wheel1 (n : ℕ) : ∀ r : ℕ, 9535 ≤ r →
    (r : ℝ) / 20 ≤ fwAffineThreshold 2 (fwMixedWheelRho 1)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) r 1
      (poolMaximum n) (fwMixedWheelError 1) := by
  intro r hr
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hrreal : (9535 : ℝ) ≤ r := by exact_mod_cast hr
  have heq : fwAffineThreshold 2 (fwMixedWheelRho 1)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) r 1
      (poolMaximum n) (fwMixedWheelError 1) =
      2 / fwMixedWheelRho 1 * ((3981035 / 10000000 : ℝ) * (3257 / 100000) * r -
        (1 / 2 + fwMixedWheelError 1)) := by
    unfold fwAffineThreshold
    field_simp
  rw [heq]
  rw [show fwMixedWheelRho 1 = (110592 / 323323 : ℝ) by rfl,
      show fwMixedWheelError 1 = (476024 / 17017 : ℝ) by rfl]
  norm_num
  nlinarith

theorem fw_prop_wheel2 (n : ℕ) : ∀ r : ℕ, 16301 ≤ r →
    (r : ℝ) / 20 ≤ fwAffineThreshold 2 (fwMixedWheelRho 2)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) r 1
      (poolMaximum n) (fwMixedWheelError 2) := by
  intro r hr
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hrreal : (16301 : ℝ) ≤ r := by exact_mod_cast hr
  have heq : fwAffineThreshold 2 (fwMixedWheelRho 2)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) r 1
      (poolMaximum n) (fwMixedWheelError 2) =
      2 / fwMixedWheelRho 2 * ((3981035 / 10000000 : ℝ) * (3257 / 100000) * r -
        (1 / 2 + fwMixedWheelError 2)) := by
    unfold fwAffineThreshold
    field_simp
  rw [heq]
  rw [show fwMixedWheelRho 2 = (221184 / 676039 : ℝ) by rfl,
      show fwMixedWheelError 2 = (18199504 / 323323 : ℝ) by rfl]
  norm_num
  nlinarith

theorem fw_prop_wheel3 (n : ℕ) : ∀ r : ℕ, 29268 ≤ r →
    (r : ℝ) / 20 ≤ fwAffineThreshold 2 (fwMixedWheelRho 3)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) r 1
      (poolMaximum n) (fwMixedWheelError 3) := by
  intro r hr
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hrreal : (29268 : ℝ) ≤ r := by exact_mod_cast hr
  have heq : fwAffineThreshold 2 (fwMixedWheelRho 3)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) r 1
      (poolMaximum n) (fwMixedWheelError 3) =
      2 / fwMixedWheelRho 3 * ((3981035 / 10000000 : ℝ) * (3257 / 100000) * r -
        (1 / 2 + fwMixedWheelError 3)) := by
    unfold fwAffineThreshold
    field_simp
  rw [heq]
  rw [show fwMixedWheelRho 3 = (884736 / 2800733 : ℝ) by rfl,
      show fwMixedWheelError 3 = (839610208 / 7436429 : ℝ) by rfl]
  norm_num
  nlinarith

theorem fw_prop_wheel4 (n : ℕ) : ∀ r : ℕ, 45398 ≤ r →
    (r : ℝ) / 20 ≤ fwAffineThreshold 2 (fwMixedWheelRho 4)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) r 1
      (poolMaximum n) (fwMixedWheelError 4) := by
  intro r hr
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hrreal : (45398 : ℝ) ≤ r := by exact_mod_cast hr
  have heq : fwAffineThreshold 2 (fwMixedWheelRho 4)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) r 1
      (poolMaximum n) (fwMixedWheelError 4) =
      2 / fwMixedWheelRho 4 * ((3981035 / 10000000 : ℝ) * (3257 / 100000) * r -
        (1 / 2 + fwMixedWheelError 4)) := by
    unfold fwAffineThreshold
    field_simp
  rw [heq]
  rw [show fwMixedWheelRho 4 = (26542080 / 86822723 : ℝ) by rfl,
      show fwMixedWheelError 4 = (150976832 / 667667 : ℝ) by rfl]
  norm_num
  nlinarith

theorem fw_prop_wheel5 (n : ℕ) : ∀ r : ℕ, 73941 ≤ r →
    (r : ℝ) / 22 ≤ fwAffineThreshold 2 (fwMixedWheelRho 5)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) r 1
      (poolMaximum n) (fwMixedWheelError 5) := by
  intro r hr
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hrreal : (73941 : ℝ) ≤ r := by exact_mod_cast hr
  have heq : fwAffineThreshold 2 (fwMixedWheelRho 5)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) r 1
      (poolMaximum n) (fwMixedWheelError 5) =
      2 / fwMixedWheelRho 5 * ((3981035 / 10000000 : ℝ) * (3257 / 100000) * r -
        (1 / 2 + fwMixedWheelError 5)) := by
    unfold fwAffineThreshold
    field_simp
  rw [heq]
  rw [show fwMixedWheelRho 5 = (955514880 / 3212440751 : ℝ) by rfl,
      show fwMixedWheelError 5 = (3025505777792 / 6685349671 : ℝ) by rfl]
  norm_num
  nlinarith

theorem fw_prop_wheel6 (n : ℕ) : ∀ r : ℕ, 115323 ≤ r →
    (r : ℝ) / 30 ≤ fwAffineThreshold 2 (fwMixedWheelRho 6)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) r 1
      (poolMaximum n) (fwMixedWheelError 6) := by
  intro r hr
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hrreal : (115323 : ℝ) ≤ r := by exact_mod_cast hr
  have heq : fwAffineThreshold 2 (fwMixedWheelRho 6)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) r 1
      (poolMaximum n) (fwMixedWheelError 6) =
      2 / fwMixedWheelRho 6 * ((3981035 / 10000000 : ℝ) * (3257 / 100000) * r -
        (1 / 2 + fwMixedWheelError 6)) := by
    unfold fwAffineThreshold
    field_simp
  rw [heq]
  rw [show fwMixedWheelRho 6 = (38220595200 / 131710070791 : ℝ) by rfl,
      show fwMixedWheelError 6 = (7722793179392 / 8529584063 : ℝ) by rfl]
  norm_num
  nlinarith

/-- The supplied linked schedules imply the final wheel entry radius. -/
theorem fw_eighth_entry_radius {n : ℕ} {R₀ last₀ R₁ last₁ R₂ last₂ R₃ last₃ R₄ last₄ R₅ last₅ R₆ last₆ R₇ last₇ : ℕ}
    {window first second third fourth fifth sixth seventh : List BTSelectedStage}
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
    (hsixthlen : sixth.length = 10)
    (hseventh : FWMixedAffineCertifiedSchedule 6 n 23
      ((3257 / 100000 : ℝ) * poolMaximum n) ((3257 / 100000 : ℝ) * poolMaximum n)
      (3981035 / 10000000) R₆ last₆ R₇ last₇ seventh)
    (hseventhlen : seventh.length = 8) :
    149908 ≤ R₇ ∧ 2 ∣ R₇ ∧ R₇ ≤ last₇ := by
  have hR₀ := fw_certified_118_radius_at_least_7118 hwindow hlen
  have hg0 := fw_schedule_lower_growth hfirst 7118 hR₀
    (fw_increment_proportional (by norm_num) (fw_prop_wheel0 n))
  have hR₁ : 9535 ≤ R₁ := by
    rw [hfirstlen] at hg0
    norm_num [fwLowerGrowth] at hg0
    exact hg0
  have hg1 := fw_schedule_lower_growth hsecond 9535 hR₁
    (fw_increment_proportional (by norm_num) (fw_prop_wheel1 n))
  have hR₂ : 16301 ≤ R₂ := by
    rw [hsecondlen] at hg1
    norm_num [fwLowerGrowth] at hg1
    exact hg1
  have hg2 := fw_schedule_lower_growth hthird 16301 hR₂
    (fw_increment_proportional (by norm_num) (fw_prop_wheel2 n))
  have hR₃ : 29268 ≤ R₃ := by
    rw [hthirdlen] at hg2
    norm_num [fwLowerGrowth] at hg2
    exact hg2
  have hg3 := fw_schedule_lower_growth hfourth 29268 hR₃
    (fw_increment_proportional (by norm_num) (fw_prop_wheel3 n))
  have hR₄ : 45398 ≤ R₄ := by
    rw [hfourthlen] at hg3
    norm_num [fwLowerGrowth] at hg3
    exact hg3
  have hg4 := fw_schedule_lower_growth hfifth 45398 hR₄
    (fw_increment_proportional (by norm_num) (fw_prop_wheel4 n))
  have hR₅ : 73941 ≤ R₅ := by
    rw [hfifthlen] at hg4
    norm_num [fwLowerGrowth] at hg4
    exact hg4
  have hg5 := fw_schedule_lower_growth hsixth 73941 hR₅
    (fw_increment_proportional (by norm_num) (fw_prop_wheel5 n))
  have hR₆ : 115323 ≤ R₆ := by
    rw [hsixthlen] at hg5
    norm_num [fwLowerGrowth] at hg5
    exact hg5
  have hg6 := fw_schedule_lower_growth hseventh 115323 hR₆
    (fw_increment_proportional (by norm_num) (fw_prop_wheel6 n))
  have hR₇ : 149908 ≤ R₇ := by
    rw [hseventhlen] at hg6
    norm_num [fwLowerGrowth] at hg6
    exact hg6
  obtain ⟨heven, hbelow⟩ := fw_certified_schedule_endpoint_from_32 hwindow (by decide)
  obtain ⟨heven₁, hbelow₁⟩ := fw_mixed_affine_schedule_endpoint hfirst heven hbelow
  obtain ⟨heven₂, hbelow₂⟩ := fw_mixed_affine_schedule_endpoint hsecond heven₁ hbelow₁
  obtain ⟨heven₃, hbelow₃⟩ := fw_mixed_affine_schedule_endpoint hthird heven₂ hbelow₂
  obtain ⟨heven₄, hbelow₄⟩ := fw_mixed_affine_schedule_endpoint hfourth heven₃ hbelow₃
  obtain ⟨heven₅, hbelow₅⟩ := fw_mixed_affine_schedule_endpoint hfifth heven₄ hbelow₄
  obtain ⟨heven₆, hbelow₆⟩ := fw_mixed_affine_schedule_endpoint hsixth heven₅ hbelow₅
  obtain ⟨heven₇, hbelow₇⟩ := fw_mixed_affine_schedule_endpoint hseventh heven₆ hbelow₆
  exact ⟨hR₇, heven₇, hbelow₇⟩

/-- After the supplied 118-, 6-, 11-, 12-, 9-, 10-, 10-, and 8-stage schedules,
start wheel 7 with a freshly checked origin. The continuation stops at
actual crossing or after 44 further stages. -/
theorem fw_eighth_affine_phase_after_seventh
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (R₀ last₀ R₁ last₁ R₂ last₂ R₃ last₃ R₄ last₄ R₅ last₅ R₆ last₆ R₇ last₇ : ℕ) (S : Finset ℕ) (window first second third fourth fifth sixth seventh : List BTSelectedStage)
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
    (hseventh : FWMixedAffineCertifiedSchedule 6 n 23
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
      (3981035 / 10000000) R₆ last₆ R₇ last₇ seventh)
    (hseventhlen : seventh.length = 8)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 S last₇ (((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth) ++ seventh)) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let M : ℝ := (3257 / 100000 : ℝ) * X
    let eta : ℝ := 3981035 / 10000000
    ∃ (final : Finset ℕ) (Rfinal lastFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final lastFinal ((((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth) ++ seventh) ++ extra) ∧
      extra.length ≤ 44 ∧ final ⊆ S ∧ final.card + 2 * Q * extra.length = S.card ∧
      (X / 23 ≤ lastFinal ∨ extra.length = 44) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages (X / 6) extra ∧
      R₇ ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ lastFinal ∧
      FWMixedAffineCertifiedSchedule 7 n 23 M M eta R₇ last₇ Rfinal lastFinal extra := by
  obtain ⟨hR, heven, hbelow⟩ :=
    fw_eighth_entry_radius hwindow hwindowlen hfirst hfirstlen hsecond hsecondlen hthird hthirdlen hfourth hfourthlen hfifth hfifthlen hsixth hsixthlen hseventh hseventhlen
  have hRweak : 139718 ≤ R₇ := by omega
  have hlen : (((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth) ++ seventh).length ≤ 184 := by
    simp [hwindowlen, hfirstlen, hsecondlen, hthirdlen, hfourthlen, hfifthlen, hsixthlen, hseventhlen]
  exact fw_eighth_affine_phase_from_184 bmor lower upper upperSharp hnlo hnhi
    batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R₇ last₇ S
    (((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth) ++ seventh) trace hlen hRweak heven hbelow

end
end Sude
