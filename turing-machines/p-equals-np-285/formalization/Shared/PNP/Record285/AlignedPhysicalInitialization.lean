import Shared.PNP.Record285.AlignedPhysicalEvents
import Shared.PNP.Record285.FirstEvent

/-! Tie the direct full-tape refinement to the actual wholly blank start and
show that its finite initialization prefix contains no designated events. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.AlignedPhysical
open Shared.Beeping
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarCoreGraph
open Shared.PNP.Record285.GrammarCoreZero
open Shared.PNP.Record285.OwnershipCore

theorem exact_expansion_first_boundary : ExpansionBoundary.exactRefinement.boundary 1 = 1 := by decide

theorem exact_zero_first_boundary : ZeroBoundary.exactRefinement.boundary 1 = 1 := by decide

theorem logical_first_action_silent : ¬ (system logicalRows).BeepAt 0 := by
  change ¬ (step logicalRows ⟨0,fun _ => 0⟩).2 = true
  decide

theorem input_second_action_beeps : (coreSystem inputRows).BeepAt 1 := by
  change (coreStep inputRows (coreStep inputRows (coreSystem inputRows).initial).1).2 = true
  decide

/-- The first coalesced logical action takes exactly one input action: an
additional step would pass the live event at input row 1. -/
theorem coalescing_first_boundary : acceptedCoalescing.boundary 1 = 1 := by
  have hz := acceptedCoalescing.boundary_zero
  have hp : 0 < acceptedCoalescing.boundary 1 := by
    simpa [hz] using acceptedCoalescing.progress 0
  have hle : acceptedCoalescing.boundary 1 ≤ 1 := by
    by_cases h : acceptedCoalescing.boundary 1 ≤ 1
    · exact h
    · have he : (system logicalRows).BeepAt 0 := by
        apply (acceptedCoalescing.event_iff 0).2
        exact ⟨1,by omega,by simpa using (show 1 < acceptedCoalescing.boundary 1 by omega),input_second_action_beeps⟩
      exact False.elim (logical_first_action_silent he)
  omega

/-- The first source state aligns with the first producer-core action boundary. -/
theorem first_producer_index : producerIndex 0 = 1 := by
  have ha := alignment 0
  have hexp : ExpansionBoundary.exactRefinement.boundary (logicalIndex 0) = 1 := by
    have h := ha.1
    change 1+SourceControllerSimulation.simulation.toEventRefinement.boundary 0 = _ at h
    rw [SourceControllerSimulation.simulation.toEventRefinement.boundary_zero] at h
    omega
  have hj : logicalIndex 0 = 1 := by
    by_cases h : logicalIndex 0 = 1
    · exact h
    · by_cases hlt : logicalIndex 0 < 1
      · have hs := ExpansionBoundary.exactRefinement.boundary_strict hlt
        rw [hexp,exact_expansion_first_boundary] at hs
        omega
      · have hs := ExpansionBoundary.exactRefinement.boundary_strict (show 1 < logicalIndex 0 by omega)
        rw [hexp,exact_expansion_first_boundary] at hs
        omega
  have hz : ZeroBoundary.exactRefinement.boundary (producerIndex 0) = 1 := by
    have h := ha.2.1
    change acceptedCoalescing.boundary (logicalIndex 0) = _ at h
    rw [hj,coalescing_first_boundary] at h
    exact h.symm
  by_cases h : producerIndex 0 = 1
  · exact h
  · by_cases hlt : producerIndex 0 < 1
    · have hs := ZeroBoundary.exactRefinement.boundary_strict hlt
      rw [hz,exact_zero_first_boundary] at hs
      omega
    · have hs := ZeroBoundary.exactRefinement.boundary_strict (show 1 < producerIndex 0 by omega)
      rw [hz,exact_zero_first_boundary] at hs
      omega

theorem producer_first_action_silent : ¬ (coreSystem producerRows).BeepAt 0 := by
  change ¬ (coreStep producerRows (coreSystem producerRows).initial).2 = true
  decide

/-- From the wholly blank tape up to the first aligned source boundary, no
marked event occurs. -/
theorem initial_prefix_silent (t : Nat) (ht : t < boundary 0) :
    ¬ Shared.PNP.Record285.machine.system.BeepAt t := by
  have hb : boundary 0 = 89806142+producerPhysicalRefinement.boundary 1 := by
    simp [boundary,ProducerFullBoundary.boundary,first_producer_index]
  by_cases hearly : t < 89806142
  · exact InitializationComplete.blank_start_entry.2 t hearly
  · intro he
    have hbase := producerPhysicalRefinement.boundary_zero
    have hlt : t-89806142 < producerPhysicalRefinement.boundary 1 := by rw [hb] at ht; omega
    have he' : GrammarOperationalRun.physicalSystem.BeepAt (t-89806142) := by
      apply (restarted_beep_offset Shared.PNP.Record285.machine.system 89806142 (t-89806142)).2
      have heq : 89806142+(t-89806142)=t := by omega
      simpa [heq] using he
    have hcore : (coreSystem producerRows).BeepAt 0 :=
      (producerPhysicalRefinement.event_iff 0).2 ⟨t-89806142,by rw [hbase]; omega,hlt,he'⟩
    exact producer_first_action_silent hcore

/-- The independently checked first literal event occurs inside the first
aligned source action, and is its only marked transition. -/
theorem first_event_in_first_source_segment :
    boundary 0 ≤ 89844409 ∧ 89844409 < boundary 1 ∧
      (∀ t, boundary 0 ≤ t → t < boundary 1 →
        (Shared.PNP.Record285.machine.system.BeepAt t ↔ t = 89844409)) := by
  have hsource : Source.controller.BeepAt 0 := by
    change (Source.controllerStep Source.controller.initial).2 = true
    rfl
  obtain ⟨t,htlo,hthi,hevent⟩ := (boundary_event_iff 0).1 hsource
  have hfirst : 89844409 ≤ t := by
    by_cases h : 89844409 ≤ t
    · exact h
    · exact False.elim (FirstEvent.first_event.2 t (by omega) hevent)
  have hlo : boundary 0 ≤ 89844409 := by
    by_cases h : boundary 0 ≤ 89844409
    · exact h
    · exact False.elim (initial_prefix_silent 89844409 (by omega) FirstEvent.first_event.1)
  have hhi : 89844409 < boundary 1 := by simpa using (show 89844409 < boundary (0+1) by omega)
  refine ⟨hlo,hhi,?_⟩
  intro u hulo huhi
  constructor
  · intro hu
    exact boundary_event_unique 0 u 89844409 hulo (by simpa using huhi) hlo
      (by simpa using hhi) hu FirstEvent.first_event.1
  · rintro rfl
    exact FirstEvent.first_event.1

end Shared.PNP.Record285.AlignedPhysical
