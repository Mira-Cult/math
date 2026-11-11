import Sude.FWMixedAffineTraceStep

/-! A certified even radius for an affine stage. The source threshold stays
real in the stage record; the separate even ceiling is used only for the
conservative radius. No gate discharge or physical placement is asserted. -/

namespace Sude
noncomputable section

/-- Rounding a strictly positive real threshold upward to the next even
natural preserves the lower bound and stays below any admissible even gap. -/
theorem fw_even_ceiling_threshold {D : ℝ} {gap : ℕ}
    (hD : 0 < D) (hgap : 2 ∣ gap) (hbound : D ≤ gap) :
    0 < 2 * ⌈D / 2⌉₊ ∧ 2 ∣ 2 * ⌈D / 2⌉₊ ∧
      D ≤ ((2 * ⌈D / 2⌉₊ : ℕ) : ℝ) ∧ 2 * ⌈D / 2⌉₊ ≤ gap := by
  have hceil : 0 < ⌈D / 2⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hlarge : D ≤ ((2 * ⌈D / 2⌉₊ : ℕ) : ℝ) := by
    have h := Nat.le_ceil (D / 2)
    push_cast
    linarith
  have hsmall : 2 * ⌈D / 2⌉₊ ≤ gap := by
    obtain ⟨k, rfl⟩ := hgap
    have hk : D / 2 ≤ (k : ℝ) := by
      push_cast at hbound
      linarith
    exact Nat.mul_le_mul_left 2 (Nat.ceil_le.mpr hk)
  exact ⟨by omega, dvd_mul_right 2 _, hlarge, hsmall⟩

/-- A fixed affine wheel's source threshold is monotone in its radius. -/
theorem fw_affine_threshold_mono_radius {g rho eta M r X C : ℝ}
    (hg : 0 ≤ g) (hrho : 0 < rho) (heta : 0 ≤ eta) (hM : 0 ≤ M)
    (hr : 0 < r) (hX : 0 < X) :
    Monotone (fun R => fwAffineThreshold g rho eta M R r X C) := by
  intro a b hab
  unfold fwAffineThreshold
  have hmul : eta * M * a / (r * X) ≤ eta * M * b / (r * X) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hab (mul_nonneg heta hM)
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hmul _) (div_nonneg hg hrho.le)


/-- Positive real AW threshold rounded upward to an even natural solely for
certified radius bookkeeping. The actual stage minimum remains real. -/
def fwMixedAffineEvenIncrement (i : Fin 8) (n R : ℕ) (M eta : ℝ) : ℕ :=
  2 * ⌈fwAffineThreshold 2 (fwMixedWheelRho i) eta M R 1 (poolMaximum n)
    (fwMixedWheelError i) / 2⌉₊

/-- A sequence of same-wheel affine stage labels records both radii and the
exact real AW threshold at each stage. The phase origin is fixed throughout;
this relation does not assert stock or physical placement. -/
inductive FWMixedAffineCertifiedSchedule (i : Fin 8) (n : ℕ) (L M Mf eta : ℝ) :
    ℕ → ℕ → ℕ → ℕ → List BTSelectedStage → Prop
  | nil (R actual : ℕ) : FWMixedAffineCertifiedSchedule i n L M Mf eta R actual R actual []
  | cons (R actual Rfinal actualFinal : ℕ) (stage : BTSelectedStage) (tail : List BTSelectedStage)
      (hbefore : (actual : ℝ) < (poolMaximum n : ℝ) / L)
      (hbelow : R ≤ actual)
      (hshift : 0 < (R : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta Mf)
      (hminimum : stage.minimum = fwAffineThreshold 2 (fwMixedWheelRho i) eta M R 1
        (poolMaximum n) (fwMixedWheelError i))
      (hpositive : 0 < stage.gap) (heven : 2 ∣ stage.gap)
      (hlower : fwAffineThreshold 2 (fwMixedWheelRho i) eta M R 1 (poolMaximum n)
        (fwMixedWheelError i) ≤ stage.gap)
      (hupper : stage.gap ≤ R)
      (hrest : FWMixedAffineCertifiedSchedule i n L M Mf eta
        (R + fwMixedAffineEvenIncrement i n R M eta) (actual + stage.gap) Rfinal actualFinal tail) :
      FWMixedAffineCertifiedSchedule i n L M Mf eta R actual Rfinal actualFinal (stage :: tail)


/-- The even ceiling does not exceed any even gap above the threshold. -/
theorem fw_mixed_affine_even_increment_le {i : Fin 8} {n R gap : ℕ} {M eta : ℝ}
    (heven : 2 ∣ gap)
    (hbound : fwAffineThreshold 2 (fwMixedWheelRho i) eta M R 1 (poolMaximum n)
      (fwMixedWheelError i) ≤ gap) :
    fwMixedAffineEvenIncrement i n R M eta ≤ gap := by
  obtain ⟨k, rfl⟩ := heven
  unfold fwMixedAffineEvenIncrement
  apply Nat.mul_le_mul_left
  apply Nat.ceil_le.mpr
  push_cast at hbound
  linarith

/-- Rounding up to the next even natural dominates the real threshold. -/
theorem fw_mixed_affine_threshold_le_increment (i : Fin 8) (n R : ℕ) (M eta : ℝ) :
    fwAffineThreshold 2 (fwMixedWheelRho i) eta M R 1 (poolMaximum n)
      (fwMixedWheelError i) ≤ fwMixedAffineEvenIncrement i n R M eta := by
  have h := Nat.le_ceil (fwAffineThreshold 2 (fwMixedWheelRho i) eta M R 1 (poolMaximum n)
    (fwMixedWheelError i) / 2)
  unfold fwMixedAffineEvenIncrement
  push_cast
  linarith

/-- A certified schedule preserves evenness and its order below actual radius. -/
theorem fw_mixed_affine_schedule_endpoint {i : Fin 8} {n : ℕ} {L M Mf eta : ℝ}
    {R actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWMixedAffineCertifiedSchedule i n L M Mf eta R actual Rfinal actualFinal stages)
    (heven : 2 ∣ R) (hbelow : R ≤ actual) :
    2 ∣ Rfinal ∧ Rfinal ≤ actualFinal := by
  induction sched with
  | nil R actual => exact ⟨heven, hbelow⟩
  | cons R actual Rfinal actualFinal stage tail hbefore hbelow' hshift hminimum
      hpositive hgapEven hlower hupper hrest ih =>
    have hinc : fwMixedAffineEvenIncrement i n R M eta ≤ stage.gap :=
      fw_mixed_affine_even_increment_le hgapEven hlower
    have hincEven : 2 ∣ fwMixedAffineEvenIncrement i n R M eta := by
      unfold fwMixedAffineEvenIncrement
      exact dvd_mul_right 2 _
    exact ih (dvd_add heven hincEven) (by omega)

/-- Any lower real gain for an affine threshold transfers to its rounded
certified radius, before making any numeric claim about crossing. -/
theorem fw_mixed_affine_certified_single_gain {i : Fin 8} {n R : ℕ} {M eta K origin : ℝ}
    (hgain : K * ((R : ℝ) - origin) ≤
      fwAffineThreshold 2 (fwMixedWheelRho i) eta M R 1 (poolMaximum n)
        (fwMixedWheelError i)) :
    (1 + K) * ((R : ℝ) - origin) ≤
      ((R + fwMixedAffineEvenIncrement i n R M eta : ℕ) : ℝ) - origin := by
  have hceil := fw_mixed_affine_threshold_le_increment i n R M eta
  push_cast
  nlinarith


end
end Sude
