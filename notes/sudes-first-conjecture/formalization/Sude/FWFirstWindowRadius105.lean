import Sude.FWFirstWindowRadiusStrong
import Sude.FWSubwheel105Enumeration
import Sude.FWWindowMonotonicity
import Sude.FWFirstWindowExactFloor
import Sude.FWFirstWheelThreeGap
import Sude.FWBaseWindowDiscrepancy

/-! A stronger conditional first-window radius bound from the exact rational
floor, exact subwheel-105 windows, and the certified base-wheel discrepancy. The
integer lower recurrence does not assert an actual crossing or the frozen
mixed recipe. -/
namespace Sude
noncomputable section

abbrev fwRadius105Count := fwFirstWindowIntegerCount
def fwRadius105Window (j R : ℕ) : ℕ :=
  let q := fwRadius105Count j R
  max (fwWheel105Cutoff (q - 1)) ((1001 * q - 6718 + 383) / 384)
def fwRadius105Step (j R : ℕ) : ℕ := R + 2 * min (fwRadius105Window j R) (R / 2)
def fwRadius105 : ℕ → ℕ
  | 0 => 32
  | j + 1 => fwRadius105Step j (fwRadius105 j)

theorem fw_radius105_count_mono (j : ℕ) : Monotone (fwRadius105Count j) := by
  intro a b hab
  unfold fwRadius105Count fwFirstWindowIntegerCount
  apply max_le_max_left
  apply Nat.div_le_div_right
  have hm := Nat.mul_le_mul_left (2 * fwFirstWindowIntegerRate j) hab
  omega

theorem fw_radius105_window_mono (j : ℕ) : Monotone (fwRadius105Window j) := by
  intro a b hab
  have hq := fw_radius105_count_mono j hab
  unfold fwRadius105Window
  apply max_le_max
  · have hh : fwRadius105Count j a - 1 ≤ fwRadius105Count j b - 1 := Nat.sub_le_sub_right hq 1
    rw [← fw_wheel105_cutoff_eq, ← fw_wheel105_cutoff_eq]
    exact fw_wheel_cutoff_mono 105 (by decide) hh
  · apply Nat.div_le_div_right
    have hm := Nat.mul_le_mul_left 1001 hq
    have hs := Nat.sub_le_sub_right hm 6718
    omega

theorem fw_radius105_step_mono (j : ℕ) : Monotone (fwRadius105Step j) := by
  intro a b hab
  have hw := fw_radius105_window_mono j hab
  have hr := Nat.div_le_div_right (c := 2) hab
  have hm := min_le_min hw hr
  unfold fwRadius105Step
  omega

theorem fw_radius105_ge_32 (j : ℕ) : 32 ≤ fwRadius105 j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [fwRadius105, fwRadius105Step]; omega

/-- The two rigorously established wheel lower bounds and exact rational
floor yield a finite integer increment lower bound. -/
theorem fw_radius105_window_cutoff {j R : ℕ} (hj : j < 118) :
    2 * min (fwRadius105Window j R) (R / 2) ≤ fwFirstWindowCutoff j R := by
  let q := fwRadius105Count j R
  let T := fwFirstWindowT j R
  let k := fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
    (Nat.totient_pos.mpr (by decide))
  have hq : q ≤ T + 1 := fw_first_window_integer_count_le hj
  have hqminus : q - 1 ≤ T := by omega
  have h15mono := fw_wheel_cutoff_mono 105 (by decide) hqminus
  have h15W := fw_subwheel_cutoff_le 105 15015 T (by decide) (by decide) (by decide)
  have hdisc : 1001 * (T + 1) ≤ 384 * k + 6718 := fw_base_wheel_cutoff_discrepancy T
  have hbound1 : fwWheel105Cutoff (q - 1) ≤ k := by
    rw [← fw_wheel105_cutoff_eq]
    exact h15mono.trans h15W
  have hbound2 : (1001 * q - 6718 + 383) / 384 ≤ k := by omega
  have hwindow : fwRadius105Window j R ≤ k := max_le hbound1 hbound2
  have hm := min_le_min_right (R / 2) hwindow
  exact Nat.mul_le_mul_left 2 hm

theorem fw_certified_schedule_radius105
    {X : ℝ} {j R actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWFirstWindowCertifiedSchedule X j R actual Rfinal actualFinal stages)
    (hlower : fwRadius105 j ≤ R) :
    fwRadius105 (j + stages.length) ≤ Rfinal := by
  induction sched with
  | nil j R actual => simpa using hlower
  | cons j R actual Rfinal actualFinal stage tail hcap hbefore hbelow hfloor hminimum
      hpos hgapEven hgapLo hgapHi hrest ih =>
    have hR : 32 ≤ R := le_trans (fw_radius105_ge_32 j) hlower
    have hbound := fw_radius105_window_cutoff (R := R) hcap
    have hnext : fwRadius105 (j + 1) ≤ R + fwFirstWindowCutoff j R := by
      have hm := fw_radius105_step_mono j hlower
      simp only [fwRadius105, fwRadius105Step] at hm ⊢
      omega
    have hfinal := ih hnext
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_radius105_118 : fwRadius105 118 = 11648 := by decide +kernel

/-- Any supplied 118-stage certified schedule starting at radius 32 ends
at radius at least 11648. -/
theorem fw_certified_118_radius_at_least_11648
    {X : ℝ} {actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWFirstWindowCertifiedSchedule X 0 32 actual Rfinal actualFinal stages)
    (hlen : stages.length = 118) : 11648 ≤ Rfinal := by
  have h := fw_certified_schedule_radius105 sched (by decide)
  rw [hlen] at h
  simpa [fw_radius105_118] using h

end
end Sude
