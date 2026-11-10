import PASoundness.M236ListSchedule
import PASoundness.Observer
/-! Connect an alternative list-stage coding to positive-rank observer addresses. -/
namespace PASoundness.M236.ListSchedule
open PASoundness.Observer

def scheduledAddress (n : Nat) : Address :=
  let p := atStage n
  ⟨p.2.length, p.1, p.2⟩

def stageForAddress (a : Address) : Nat := stage a.certificate a.coordinates

theorem scheduled_admissible (n : Nat) : Admissible .legacy (scheduledAddress n) := by
  refine ⟨rfl, ?_⟩
  intro _
  change 0 < (atStage n).2.length
  cases h : (atStage n).2 with
  | nil => exact False.elim (atStage_nonempty n h)
  | cons x xs => simp

theorem scheduled_stageForAddress (a : Address) (ha : Admissible .legacy a) :
    scheduledAddress (stageForAddress a) = a := by
  have hp : 0 < a.rank := ha.2 rfl
  have hn : a.coordinates ≠ [] := by
    intro h
    have hl := ha.1
    rw [h] at hl
    simp at hl
    omega
  unfold scheduledAddress stageForAddress
  rw [at_stage a.certificate a.coordinates hn]
  cases a
  simp_all [Admissible]

theorem stageFor_scheduledAddress (n : Nat) : stageForAddress (scheduledAddress n) = n := by
  exact stage_at n

/-- Every admissible positive-rank address occurs at one finite stage. -/
theorem exact_coverage (a : Address) (ha : Admissible .legacy a) :
    ∃! n, scheduledAddress n = a := by
  refine ⟨stageForAddress a, scheduled_stageForAddress a ha, ?_⟩
  intro n hn
  have h := congrArg stageForAddress hn
  simpa only [stageFor_scheduledAddress] using h
end PASoundness.M236.ListSchedule
