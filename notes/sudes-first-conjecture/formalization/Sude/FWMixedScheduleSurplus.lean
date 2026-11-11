import Sude.FWFirstWindowCertifiedRadius
import Sude.FWMixedAffineCertifiedStep

/-! Selected-gap surplus is not discarded by the two-radius schedules.
These deterministic accounting statements assume a supplied schedule; they
assert neither a positive surplus nor existence, numerical gates or crossing. -/
namespace Sude
noncomputable section

/-- A first-window schedule cannot decrease the actual-minus-certified
radius surplus. The inequality is stated without truncated subtraction. -/
theorem fw_first_window_schedule_surplus
    {X : ℝ} {j R actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWFirstWindowCertifiedSchedule X j R actual Rfinal actualFinal stages) :
    Rfinal + actual ≤ actualFinal + R := by
  induction sched with
  | nil j R actual => omega
  | cons j R actual Rfinal actualFinal stage tail hcap hbefore hbelow hfloor hminimum
      hpositive heven hlower hupper hrest ih =>
    omega

/-- The same surplus accounting for any single-wheel certified affine phase. -/
theorem fw_affine_schedule_surplus
    {i : Fin 8} {n : ℕ} {L M Mf eta : ℝ}
    {R actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWMixedAffineCertifiedSchedule i n L M Mf eta R actual Rfinal actualFinal stages) :
    Rfinal + actual ≤ actualFinal + R := by
  induction sched with
  | nil R actual => omega
  | cons R actual Rfinal actualFinal stage tail hbefore hbelow hshift hminimum
      hpositive heven hlower hupper hrest ih =>
    have hinc := fw_mixed_affine_even_increment_le heven hlower
    omega

/-- When the initial actual radius dominates the certified radius, the exact
initial surplus is retained at the final radius. -/
theorem fw_first_window_schedule_retains_surplus
    {X : ℝ} {j R actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWFirstWindowCertifiedSchedule X j R actual Rfinal actualFinal stages)
    (hbelow : R ≤ actual) :
    Rfinal + (actual - R) ≤ actualFinal := by
  have h := fw_first_window_schedule_surplus sched
  omega

/-- The affine phase retains the exact initial actual-minus-certified surplus. -/
theorem fw_affine_schedule_retains_surplus
    {i : Fin 8} {n : ℕ} {L M Mf eta : ℝ}
    {R actual Rfinal actualFinal : ℕ} {stages : List BTSelectedStage}
    (sched : FWMixedAffineCertifiedSchedule i n L M Mf eta R actual Rfinal actualFinal stages)
    (hbelow : R ≤ actual) :
    Rfinal + (actual - R) ≤ actualFinal := by
  have h := fw_affine_schedule_surplus sched
  omega

end
end Sude
