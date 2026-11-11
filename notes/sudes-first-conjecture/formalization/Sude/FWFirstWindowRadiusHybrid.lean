import Sude.FWFirstWindowRadiusStrong
import Sude.FWSubwheel15Enumeration
import Sude.FWWindowMonotonicity
import Sude.FWFirstWindowExactFloor
import Sude.FWFirstWheelThreeGap
import Sude.FWBaseWindowDiscrepancy

/-! A stronger conditional first-window radius bound from the exact rational
floor, exact subwheel-15 windows, and the certified base-wheel discrepancy. The
integer lower recurrence does not assert an actual crossing or the frozen
mixed recipe. -/
namespace Sude
noncomputable section

abbrev fwHybridCount := fwFirstWindowIntegerCount
def fwHybridWindow (j R : ℕ) : ℕ :=
  let q := fwHybridCount j R
  max (fwWheel15Cutoff (q - 1)) ((1001 * q - 6718 + 383) / 384)
def fwHybridStep (j R : ℕ) : ℕ := R + 2 * min (fwHybridWindow j R) (R / 2)
def fwHybridRadius : ℕ → ℕ
  | 0 => 32
  | j + 1 => fwHybridStep j (fwHybridRadius j)

theorem fw_hybrid_count_mono (j : ℕ) : Monotone (fwHybridCount j) := by
  intro a b hab
  unfold fwHybridCount fwFirstWindowIntegerCount
  apply max_le_max_left
  apply Nat.div_le_div_right
  have hm := Nat.mul_le_mul_left (2 * fwFirstWindowIntegerRate j) hab
  omega

theorem fw_hybrid_window_mono (j : ℕ) : Monotone (fwHybridWindow j) := by
  intro a b hab
  have hq := fw_hybrid_count_mono j hab
  unfold fwHybridWindow
  apply max_le_max
  · have hh : fwHybridCount j a - 1 ≤ fwHybridCount j b - 1 := Nat.sub_le_sub_right hq 1
    rw [← fw_wheel15_cutoff_eq, ← fw_wheel15_cutoff_eq]
    exact fw_wheel_cutoff_mono 15 (by decide) hh
  · apply Nat.div_le_div_right
    have hm := Nat.mul_le_mul_left 1001 hq
    have hs := Nat.sub_le_sub_right hm 6718
    omega

theorem fw_hybrid_step_mono (j : ℕ) : Monotone (fwHybridStep j) := by
  intro a b hab
  have hw := fw_hybrid_window_mono j hab
  have hr := Nat.div_le_div_right (c := 2) hab
  have hm := min_le_min hw hr
  unfold fwHybridStep
  omega

theorem fw_hybrid_radius_ge_32 (j : ℕ) : 32 ≤ fwHybridRadius j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [fwHybridRadius, fwHybridStep]; omega

/-- The two rigorously established wheel lower bounds and exact rational
floor yield a finite integer increment lower bound. -/
theorem fw_hybrid_window_cutoff {j R : ℕ} (hj : j < 118) :
    2 * min (fwHybridWindow j R) (R / 2) ≤ fwFirstWindowCutoff j R := by
  let q := fwHybridCount j R
  let T := fwFirstWindowT j R
  let k := fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
    (Nat.totient_pos.mpr (by decide))
  have hq : q ≤ T + 1 := fw_first_window_integer_count_le hj
  have hqminus : q - 1 ≤ T := by omega
  have h15mono := fw_wheel_cutoff_mono 15 (by decide) hqminus
  have h15W := fw_subwheel_cutoff_le 15 15015 T (by decide) (by decide) (by decide)
  have hdisc : 1001 * (T + 1) ≤ 384 * k + 6718 := fw_base_wheel_cutoff_discrepancy T
  have hbound1 : fwWheel15Cutoff (q - 1) ≤ k := by
    rw [← fw_wheel15_cutoff_eq]
    exact h15mono.trans h15W
  have hbound2 : (1001 * q - 6718 + 383) / 384 ≤ k := by omega
  have hwindow : fwHybridWindow j R ≤ k := max_le hbound1 hbound2
  have hm := min_le_min_right (R / 2) hwindow
  exact Nat.mul_le_mul_left 2 hm

theorem fw_certified_schedule_hybrid_radius
    {X : ℝ} {j R actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWFirstWindowCertifiedSchedule X j R actual Rfinal actualFinal stages)
    (hlower : fwHybridRadius j ≤ R) :
    fwHybridRadius (j + stages.length) ≤ Rfinal := by
  induction sched with
  | nil j R actual => simpa using hlower
  | cons j R actual Rfinal actualFinal stage tail hcap hbefore hbelow hfloor hminimum
      hpos hgapEven hgapLo hgapHi hrest ih =>
    have hR : 32 ≤ R := le_trans (fw_hybrid_radius_ge_32 j) hlower
    have hbound := fw_hybrid_window_cutoff (R := R) hcap
    have hnext : fwHybridRadius (j + 1) ≤ R + fwFirstWindowCutoff j R := by
      have hm := fw_hybrid_step_mono j hlower
      simp only [fwHybridRadius, fwHybridStep] at hm ⊢
      omega
    have hfinal := ih hnext
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_hybrid_radius_118 : fwHybridRadius 118 = 10116 := by decide +kernel

/-- Any supplied 118-stage certified schedule starting at radius 32 ends
at radius at least 10116. -/
theorem fw_certified_118_radius_at_least_10116
    {X : ℝ} {actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWFirstWindowCertifiedSchedule X 0 32 actual Rfinal actualFinal stages)
    (hlen : stages.length = 118) : 10116 ≤ Rfinal := by
  have h := fw_certified_schedule_hybrid_radius sched (by decide)
  rw [hlen] at h
  simpa [fw_hybrid_radius_118] using h

end
end Sude
