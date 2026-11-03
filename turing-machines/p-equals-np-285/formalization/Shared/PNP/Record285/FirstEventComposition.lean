import Shared.PNP.Record285.FirstEventCertificate
import Shared.PNP.Record285.InitializationReturn

/-! Conditional composition of the first post-entry event; the candidate-entry
premise is supplied by the full initialization certificate. -/
namespace Shared.PNP.Record285.FirstEventComposition
open Shared.Beeping
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.InitializationComposition
open Shared.PNP.Record285.InitializationReturn (related_read)
open Shared.PNP.Record285.FirstEventCertificate

theorem run_offset {C : Type} (sys : EventSystem C) (start t : Nat) :
    (EventSystem.mk (sys.run start) sys.step).run t = sys.run (start+t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [EventSystem.run_succ, ih, Nat.add_succ, EventSystem.run_succ]

theorem beep_offset {C : Type} (sys : EventSystem C) (start t : Nat) :
    (EventSystem.mk (sys.run start) sys.step).BeepAt t ↔ sys.BeepAt (start+t) := by
  change (sys.step ((EventSystem.mk (sys.run start) sys.step).run t)).2 = true ↔ _
  rw [run_offset]
  rfl

theorem pre_event_config_of_entry
    (hentry : Rel candidate (Record285.machine.system.run 89806142)) :
    Rel c12 (Record285.machine.system.run 89844409) := by
  have h := (silent_physical Record285.machine candidate
    (Record285.machine.system.run 89806142) hentry 38267 c12 silent_to_event).1
  change Rel c12 ((EventSystem.mk (Record285.machine.system.run 89806142)
    Record285.machine.system.step).run 38267) at h
  rw [run_offset] at h
  exact h

/-- From the candidate entry configuration, the next 38,267 transitions are
silent and the following transition is marked. -/
theorem first_event_of_entry
    (hentry : Rel candidate (Record285.machine.system.run 89806142)) :
    Record285.machine.system.BeepAt 89844409 ∧
      ∀ t, 89806142 ≤ t → t < 89844409 → ¬ Record285.machine.system.BeepAt t := by
  have hseg := silent_physical Record285.machine candidate
    (Record285.machine.system.run 89806142) hentry 38267 c12 silent_to_event
  have hcfg := pre_event_config_of_entry hentry
  have hs : (Record285.machine.system.run 89844409).state.val = 121 := by
    have heq : (Record285.machine.system.run 89844409).state = c12.state := hcfg.1.symm
    rw [heq]
    exact event_shape.1
  have hr : (Record285.machine.system.run 89844409).tape
      (Record285.machine.system.run 89844409).head = true := by
    have hh := related_read c12 (Record285.machine.system.run 89844409) hcfg
    rw [event_shape.2] at hh
    exact hh
  constructor
  · exact (ArtifactEndpoint.literal_beep 89844409).2 ⟨hs,hr⟩
  · intro t hlo hhi he
    have ht : t = 89806142 + (t-89806142) := by omega
    have hb := hseg.2 (t-89806142) (by omega)
    apply hb
    apply (beep_offset Record285.machine.system 89806142 (t-89806142)).2
    simpa only [← ht] using he

end Shared.PNP.Record285.FirstEventComposition
