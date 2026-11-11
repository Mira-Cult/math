import Sude.FWFirstWindowRadius118
import Sude.FWFirstWindowExactFloor
import Sude.FWFirstWheelThreeGap
import Sude.FWBaseWindowDiscrepancy

/-! A stronger conditional first-window radius bound from the exact rational
floor, divisibility by three, and the certified base-wheel discrepancy. The
integer lower recurrence does not assert an actual crossing or the frozen
mixed recipe. -/
namespace Sude
noncomputable section

abbrev fwStrongCount := fwFirstWindowIntegerCount
def fwStrongWindow (j R : ℕ) : ℕ :=
  let q := fwStrongCount j R
  max (q + q / 2) ((1001 * q - 6718 + 383) / 384)
def fwStrongStep (j R : ℕ) : ℕ := R + 2 * min (fwStrongWindow j R) (R / 2)
def fwStrongRadius : ℕ → ℕ
  | 0 => 32
  | j + 1 => fwStrongStep j (fwStrongRadius j)

theorem fw_strong_count_mono (j : ℕ) : Monotone (fwStrongCount j) := by
  intro a b hab
  unfold fwStrongCount fwFirstWindowIntegerCount
  apply max_le_max_left
  apply Nat.div_le_div_right
  have hm := Nat.mul_le_mul_left (2 * fwFirstWindowIntegerRate j) hab
  omega

theorem fw_strong_window_mono (j : ℕ) : Monotone (fwStrongWindow j) := by
  intro a b hab
  have hq := fw_strong_count_mono j hab
  unfold fwStrongWindow
  apply max_le_max
  · have hh := Nat.div_le_div_right (c := 2) hq
    omega
  · apply Nat.div_le_div_right
    have hm := Nat.mul_le_mul_left 1001 hq
    have hs := Nat.sub_le_sub_right hm 6718
    omega

theorem fw_strong_step_mono (j : ℕ) : Monotone (fwStrongStep j) := by
  intro a b hab
  have hw := fw_strong_window_mono j hab
  have hr := Nat.div_le_div_right (c := 2) hab
  have hm := min_le_min hw hr
  unfold fwStrongStep
  omega

theorem fw_strong_radius_ge_32 (j : ℕ) : 32 ≤ fwStrongRadius j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [fwStrongRadius, fwStrongStep]; omega

/-- The two rigorously established wheel lower bounds and exact rational
floor yield a finite integer increment lower bound. -/
theorem fw_strong_window_cutoff {j R : ℕ} (hj : j < 118) :
    2 * min (fwStrongWindow j R) (R / 2) ≤ fwFirstWindowCutoff j R := by
  let q := fwStrongCount j R
  let T := fwFirstWindowT j R
  let k := fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
    (Nat.totient_pos.mpr (by decide))
  have hq : q ≤ T + 1 := fw_first_window_integer_count_le hj
  have hthree : T + 1 + (T + 1) / 2 ≤ k := fw_first_wheel_cutoff_three_lower T
  have hdisc : 1001 * (T + 1) ≤ 384 * k + 6718 := fw_base_wheel_cutoff_discrepancy T
  have hhalf : q / 2 ≤ (T + 1) / 2 := Nat.div_le_div_right hq
  have hbound1 : q + q / 2 ≤ k := by omega
  have hbound2 : (1001 * q - 6718 + 383) / 384 ≤ k := by omega
  have hwindow : fwStrongWindow j R ≤ k := max_le hbound1 hbound2
  have hm := min_le_min_right (R / 2) hwindow
  exact Nat.mul_le_mul_left 2 hm

theorem fw_certified_schedule_strong_radius
    {X : ℝ} {j R actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWFirstWindowCertifiedSchedule X j R actual Rfinal actualFinal stages)
    (hlower : fwStrongRadius j ≤ R) :
    fwStrongRadius (j + stages.length) ≤ Rfinal := by
  induction sched with
  | nil j R actual => simpa using hlower
  | cons j R actual Rfinal actualFinal stage tail hcap hbefore hbelow hfloor hminimum
      hpos hgapEven hgapLo hgapHi hrest ih =>
    have hR : 32 ≤ R := le_trans (fw_strong_radius_ge_32 j) hlower
    have hbound := fw_strong_window_cutoff (R := R) hcap
    have hnext : fwStrongRadius (j + 1) ≤ R + fwFirstWindowCutoff j R := by
      have hm := fw_strong_step_mono j hlower
      simp only [fwStrongRadius, fwStrongStep] at hm ⊢
      omega
    have hfinal := ih hnext
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_strong_radius_118 : fwStrongRadius 118 = 7118 := by decide +kernel

/-- Any supplied 118-stage certified schedule starting at radius 32 ends
at radius at least 7118. -/
theorem fw_certified_118_radius_at_least_7118
    {X : ℝ} {actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWFirstWindowCertifiedSchedule X 0 32 actual Rfinal actualFinal stages)
    (hlen : stages.length = 118) : 7118 ≤ Rfinal := by
  have h := fw_certified_schedule_strong_radius sched (by decide)
  rw [hlen] at h
  simpa [fw_strong_radius_118] using h

end
end Sude
