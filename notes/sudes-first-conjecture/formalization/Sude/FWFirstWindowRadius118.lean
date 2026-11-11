import Sude.FWFirstWindowCertifiedRadius
import Sude.FWFirstWindowCoarseStep

/-! A conservative two-radius first-window trace that completes all 118
stages has certified radius at least 1108. This uses a weaker integer
recurrence, not a computation of the exact wheel-window sequence; no
crossing or frozen mixed-recipe claim is made. -/
namespace Sude
noncomputable section

def fwCoarseWindowStep (R : ℕ) : ℕ := R + 2 * max 1 ((2 * R + 69) / 138)

def fwCoarseWindowRadius : ℕ → ℕ
  | 0 => 32
  | j + 1 => fwCoarseWindowStep (fwCoarseWindowRadius j)

theorem fw_coarse_window_step_mono : Monotone fwCoarseWindowStep := by
  intro a b hab
  have hh : (2 * a + 69) / 138 ≤ (2 * b + 69) / 138 :=
    Nat.div_le_div_right (by omega)
  have hm : max 1 ((2 * a + 69) / 138) ≤ max 1 ((2 * b + 69) / 138) :=
    max_le_max_left 1 hh
  simp only [fwCoarseWindowStep]
  omega

theorem fw_coarse_window_radius_ge_32 (j : ℕ) : 32 ≤ fwCoarseWindowRadius j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [fwCoarseWindowRadius, fwCoarseWindowStep]; omega

theorem fw_certified_schedule_coarse_radius
    {X : ℝ} {j R actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWFirstWindowCertifiedSchedule X j R actual Rfinal actualFinal stages)
    (hlower : fwCoarseWindowRadius j ≤ R) :
    fwCoarseWindowRadius (j + stages.length) ≤ Rfinal := by
  induction sched with
  | nil j R actual => simpa using hlower
  | cons j R actual Rfinal actualFinal stage tail hcap hbefore hbelow hfloor hminimum
      hpos hgapEven hgapLo hgapHi hrest ih =>
    have hR : 32 ≤ R := le_trans (fw_coarse_window_radius_ge_32 j) hlower
    have hbound := fw_first_window_coarse_cutoff hcap hR
    have hnext : fwCoarseWindowRadius (j + 1) ≤ R + fwFirstWindowCutoff j R := by
      have hm := fw_coarse_window_step_mono hlower
      simp only [fwCoarseWindowRadius, fwCoarseWindowStep] at hm ⊢
      omega
    have hfinal := ih hnext
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_coarse_window_118 : fwCoarseWindowRadius 118 = 1108 := by decide +kernel

theorem fw_certified_118_radius_at_least_1108
    {X : ℝ} {actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWFirstWindowCertifiedSchedule X 0 32 actual Rfinal actualFinal stages)
    (hlen : stages.length = 118) : 1108 ≤ Rfinal := by
  have h := fw_certified_schedule_coarse_radius sched (by decide)
  rw [hlen] at h
  simpa [fw_coarse_window_118] using h

end
end Sude
