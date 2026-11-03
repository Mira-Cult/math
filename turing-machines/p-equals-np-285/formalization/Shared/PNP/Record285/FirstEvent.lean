import Shared.PNP.Record285.InitializationComplete
import Shared.PNP.Record285.FirstEventComposition
import Shared.PNP.Record285.FirstEventLayout

/-! The exact first marked event in the literal blank-start machine. This
finite theorem does not prove any eventual event behavior. -/
namespace Shared.PNP.Record285.FirstEvent
open Shared.PNP.Record285.InitializationComplete
open Shared.PNP.Record285.FirstEventComposition

theorem first_event :
    Record285.machine.system.BeepAt 89844409 ∧
      ∀ t, t < 89844409 → ¬ Record285.machine.system.BeepAt t := by
  obtain ⟨he, hs⟩ := first_event_of_entry blank_start_entry.1
  refine ⟨he, ?_⟩
  intro t ht
  by_cases h : t < 89806142
  · exact blank_start_entry.2 t h
  · exact hs t (by omega) ht

/-- The anchor and preceding zero fields fix the location of fields 5 and 6. -/
theorem first_event_bank_prefix :
    (Record285.machine.system.run 89844409).tape 3 = true ∧
    (Record285.machine.system.run 89844409).tape 4 = false ∧
      ∀ i : Nat, i < 5 →
        (Record285.machine.system.run 89844409).tape (5+2*(i:Int)) = true ∧
        (Record285.machine.system.run 89844409).tape (6+2*(i:Int)) = false := by
  have h := pre_event_config_of_entry blank_start_entry.1
  exact ⟨(FirstEventLayout.anchor _ h).1, (FirstEventLayout.anchor _ h).2,
    FirstEventLayout.first_five_fields _ h⟩

/-- Physical unary fields 5 and 6 immediately before that transition. -/
theorem first_event_fields :
    (Record285.machine.system.run 89844409).tape 15 = true ∧
    (Record285.machine.system.run 89844409).tape 16 = false ∧
    (Record285.machine.system.run 89844409).tape 17 = true ∧
    (Record285.machine.system.run 89844409).tape 18 = true ∧
    (Record285.machine.system.run 89844409).tape 19 = false :=
  FirstEventLayout.field_five_six _ (pre_event_config_of_entry blank_start_entry.1)

end Shared.PNP.Record285.FirstEvent
