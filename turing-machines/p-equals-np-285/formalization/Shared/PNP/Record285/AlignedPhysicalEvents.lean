import Shared.PNP.Record285.AlignedPhysical
import Shared.Beeping.RefinementIntervals

/-! Exact event accounting between successive aligned full-tape boundaries. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.AlignedPhysical
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.GrammarCoreGraph
open Shared.PNP.Record285.GrammarCoreZero
open Shared.PNP.Record285.Grammar

theorem projection_event (n : Nat) :
    (system RegisterProjection.originalRows).BeepAt n ↔ (system expandedRows).BeepAt n := by
  have h := (RegisterProjection.step_related RegisterProjection.lift RegisterProjection.lift_injective
    RegisterProjection.originalRows expandedRows RegisterProjection.projection_checked _ _
    (RegisterProjection.related_run n)).1
  change (step RegisterProjection.originalRows ((system RegisterProjection.originalRows).run n)).2 = true ↔
    (step expandedRows ((system expandedRows).run n)).2 = true
  rw [h]

theorem shifted_expanded_event (t : Nat) :
    SourceControllerSimulation.shiftedGraph.BeepAt t ↔ (system expandedRows).BeepAt (1+t) :=
  (SourceControllerSimulation.shifted_beepAt t).trans (projection_event (1+t))

theorem source_expanded_event (i : Nat) :
    Source.controller.BeepAt i ↔
      (system expandedRows).HasEvent (ExpansionBoundary.exactRefinement.boundary (logicalIndex i))
        (ExpansionBoundary.exactRefinement.boundary (logicalIndex (i+1))) := by
  let r := SourceControllerSimulation.simulation.toEventRefinement
  have hstart := (alignment i).1
  have hstop := (alignment (i+1)).1
  change 1+r.boundary i = _ at hstart
  change 1+r.boundary (i+1) = _ at hstop
  rw [r.event_iff i]
  constructor
  · rintro ⟨t,htlo,hthi,he⟩
    refine ⟨1+t,?_,?_,(shifted_expanded_event t).1 he⟩
    · rw [←hstart]; omega
    · rw [←hstop]; omega
  · rintro ⟨u,hulo,huhi,he⟩
    have hu : 1 ≤ u := by rw [←hstart] at hulo; omega
    refine ⟨u-1,?_,?_,?_⟩
    · rw [←hstart] at hulo; omega
    · rw [←hstop] at huhi; omega
    · apply (shifted_expanded_event (u-1)).2
      have heq : 1+(u-1)=u := by omega
      simpa [heq] using he

theorem source_expanded_unique (i : Nat) :
    (system expandedRows).UniqueEvents (ExpansionBoundary.exactRefinement.boundary (logicalIndex i))
      (ExpansionBoundary.exactRefinement.boundary (logicalIndex (i+1))) := by
  let r := SourceControllerSimulation.simulation.toEventRefinement
  have hstart := (alignment i).1
  have hstop := (alignment (i+1)).1
  change 1+r.boundary i = _ at hstart
  change 1+r.boundary (i+1) = _ at hstop
  intro a b halo hahi hblo hbhi ha hb
  rw [←hstart] at halo hblo
  rw [←hstop] at hahi hbhi
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hsa : SourceControllerSimulation.shiftedGraph.BeepAt (a-1) := by
    apply (shifted_expanded_event (a-1)).2
    have heq : 1+(a-1)=a := by omega
    simpa [heq] using ha
  have hsb : SourceControllerSimulation.shiftedGraph.BeepAt (b-1) := by
    apply (shifted_expanded_event (b-1)).2
    have heq : 1+(b-1)=b := by omega
    simpa [heq] using hb
  have heq := r.event_unique i (a-1) (b-1) (by omega) (by omega) (by omega) (by omega) hsa hsb
  omega

theorem restarted_interval_event (lo hi : Nat) :
    GrammarOperationalRun.physicalSystem.HasEvent lo hi ↔
      Shared.PNP.Record285.machine.system.HasEvent (89806142+lo) (89806142+hi) := by
  constructor
  · rintro ⟨t,hlo,hhi,he⟩
    exact ⟨89806142+t,by omega,by omega,
      (restarted_beep_offset Shared.PNP.Record285.machine.system 89806142 t).1 he⟩
  · rintro ⟨t,hlo,hhi,he⟩
    have ht : 89806142 ≤ t := by omega
    refine ⟨t-89806142,by omega,by omega,?_⟩
    apply (restarted_beep_offset Shared.PNP.Record285.machine.system 89806142 (t-89806142)).2
    have heq : 89806142+(t-89806142)=t := by omega
    simpa [heq] using he

theorem restarted_interval_unique (lo hi : Nat)
    (h : GrammarOperationalRun.physicalSystem.UniqueEvents lo hi) :
    Shared.PNP.Record285.machine.system.UniqueEvents (89806142+lo) (89806142+hi) := by
  intro a b halo hahi hblo hbhi ha hb
  have ha1 : 89806142 ≤ a := by omega
  have hb1 : 89806142 ≤ b := by omega
  have hsa : GrammarOperationalRun.physicalSystem.BeepAt (a-89806142) := by
    apply (restarted_beep_offset Shared.PNP.Record285.machine.system 89806142 (a-89806142)).2
    have heq : 89806142+(a-89806142)=a := by omega
    simpa [heq] using ha
  have hsb : GrammarOperationalRun.physicalSystem.BeepAt (b-89806142) := by
    apply (restarted_beep_offset Shared.PNP.Record285.machine.system 89806142 (b-89806142)).2
    have heq : 89806142+(b-89806142)=b := by omega
    simpa [heq] using hb
  have heq := h (a-89806142) (b-89806142) (by omega) (by omega) (by omega) (by omega) hsa hsb
  omega

/-- Each source event occurs exactly when its full-tape physical segment has
an event; silent actions have no spurious physical events. -/
theorem boundary_event_iff (i : Nat) :
    Source.controller.BeepAt i ↔
      Shared.PNP.Record285.machine.system.HasEvent (boundary i) (boundary (i+1)) := by
  let j := logicalIndex i
  let j' := logicalIndex (i+1)
  let m := producerIndex i
  let m' := producerIndex (i+1)
  have hstart := (alignment i).2.1
  have hstop := (alignment (i+1)).2.1
  change acceptedCoalescing.boundary j = ZeroBoundary.exactRefinement.boundary m at hstart
  change acceptedCoalescing.boundary j' = ZeroBoundary.exactRefinement.boundary m' at hstop
  calc
    _ ↔ (system expandedRows).HasEvent (ExpansionBoundary.exactRefinement.boundary j)
        (ExpansionBoundary.exactRefinement.boundary j') := source_expanded_event i
    _ ↔ (system logicalRows).HasEvent j j' :=
      (ExpansionBoundary.exactRefinement.interval_event_iff j j').symm
    _ ↔ (coreSystem inputRows).HasEvent (acceptedCoalescing.boundary j) (acceptedCoalescing.boundary j') :=
      acceptedCoalescing.interval_event_iff j j'
    _ ↔ (coreSystem producerRows).HasEvent m m' := by
      rw [hstart,hstop]
      exact (ZeroBoundary.exactRefinement.interval_event_iff m m').symm
    _ ↔ GrammarOperationalRun.physicalSystem.HasEvent (producerPhysicalRefinement.boundary m)
        (producerPhysicalRefinement.boundary m') := producerPhysicalRefinement.interval_event_iff m m'
    _ ↔ Shared.PNP.Record285.machine.system.HasEvent (boundary i) (boundary (i+1)) := by
      simpa [boundary,ProducerFullBoundary.boundary,m,m'] using
        restarted_interval_event (producerPhysicalRefinement.boundary m) (producerPhysicalRefinement.boundary m')

/-- At most one marked event can occur in the physical segment for one source
action, so the event correspondence preserves exact counts. -/
theorem boundary_event_unique (i : Nat) :
    Shared.PNP.Record285.machine.system.UniqueEvents (boundary i) (boundary (i+1)) := by
  let j := logicalIndex i
  let j' := logicalIndex (i+1)
  let m := producerIndex i
  let m' := producerIndex (i+1)
  have hstart := (alignment i).2.1
  have hstop := (alignment (i+1)).2.1
  change acceptedCoalescing.boundary j = ZeroBoundary.exactRefinement.boundary m at hstart
  change acceptedCoalescing.boundary j' = ZeroBoundary.exactRefinement.boundary m' at hstop
  have he := source_expanded_unique i
  have hl : (system logicalRows).UniqueEvents j j' :=
    (ExpansionBoundary.exactRefinement.interval_unique_iff j j').2 he
  have hin := (acceptedCoalescing.interval_unique_iff j j').1 hl
  rw [hstart,hstop] at hin
  have hp := (ZeroBoundary.exactRefinement.interval_unique_iff m m').2 hin
  have hphysical := (producerPhysicalRefinement.interval_unique_iff m m').1 hp
  simpa [boundary,ProducerFullBoundary.boundary,m,m'] using
    restarted_interval_unique (producerPhysicalRefinement.boundary m) (producerPhysicalRefinement.boundary m') hphysical

end Shared.PNP.Record285.AlignedPhysical

namespace Shared.PNP.Record285.AlignedPhysical
open Shared.Beeping

/-- Every reachable source action has a positive finite literal run between
complete related configurations, with its event count preserved exactly. -/
theorem source_action_physical_segment (i : Nat) :
    Rel (Source.controller.run i) (Shared.PNP.Record285.machine.system.run (boundary i)) ∧
    boundary i < boundary (i+1) ∧
    Rel (Source.controller.run (i+1))
      (Shared.PNP.Record285.machine.system.advance
        (Shared.PNP.Record285.machine.system.run (boundary i)) (boundary (i+1)-boundary i)) ∧
    (Source.controller.BeepAt i ↔
      Shared.PNP.Record285.machine.system.HasEvent (boundary i) (boundary (i+1))) ∧
    Shared.PNP.Record285.machine.system.UniqueEvents (boundary i) (boundary (i+1)) := by
  have hp := boundary_strict (show i < i+1 by omega)
  refine ⟨related_at_boundary i,hp,?_,boundary_event_iff i,boundary_event_unique i⟩
  have heq : boundary i+(boundary (i+1)-boundary i) = boundary (i+1) := by omega
  rw [← EventSystem.run_add,heq]
  exact related_at_boundary (i+1)

end Shared.PNP.Record285.AlignedPhysical

namespace Shared.PNP.Record285.AlignedPhysical
open Shared.Beeping
open Shared.PNP.Record285.Grammar

/-- The physical execution restarted at the first source boundary. The
finite blank-start initialization precedes this target system. -/
noncomputable def postInitialization : EventSystem (Shared.Beeping.Machines.Config 285) :=
  ⟨Shared.PNP.Record285.machine.system.run (boundary 0),Shared.PNP.Record285.machine.step⟩

noncomputable def relativeBoundary (i : Nat) : Nat := boundary i-boundary 0

theorem initial_le_boundary (i : Nat) : boundary 0 ≤ boundary i := by
  cases i with
  | zero => exact Nat.le_refl _
  | succ i => exact Nat.le_of_lt (boundary_strict (by omega : 0 < i+1))

theorem relativeBoundary_offset (i : Nat) : boundary 0+relativeBoundary i = boundary i := by
  have h := initial_le_boundary i
  simp only [relativeBoundary]
  omega

theorem post_run (t : Nat) :
    postInitialization.run t = Shared.PNP.Record285.machine.system.run (boundary 0+t) := by
  exact restarted_run_offset Shared.PNP.Record285.machine.system (boundary 0) t

theorem post_beep (t : Nat) :
    postInitialization.BeepAt t ↔ Shared.PNP.Record285.machine.system.BeepAt (boundary 0+t) := by
  exact restarted_beep_offset Shared.PNP.Record285.machine.system (boundary 0) t

/-- A direct, cofinal full-configuration refinement from the source controller
to the literal physical run after its finite blank-start initialization. -/
noncomputable def refinement : EventRefinement Source.controller postInitialization where
  Rel := Rel
  boundary := relativeBoundary
  boundary_zero := by simp [relativeBoundary]
  progress := by
    intro i
    have hs := boundary_strict (show i < i+1 by omega)
    have h0 := initial_le_boundary i
    simp only [relativeBoundary]
    omega
  related := by
    intro i
    rw [post_run,relativeBoundary_offset]
    exact related_at_boundary i
  event_iff := by
    intro i
    rw [boundary_event_iff i]
    constructor
    · rintro ⟨t,hlo,hhi,he⟩
      have h0 := initial_le_boundary i
      have ht : boundary 0 ≤ t := by omega
      refine ⟨t-boundary 0,?_,?_,?_⟩
      · have hh := relativeBoundary_offset i
        omega
      · have hh := relativeBoundary_offset (i+1)
        omega
      · apply (post_beep (t-boundary 0)).2
        have heq : boundary 0+(t-boundary 0)=t := by omega
        simpa [heq] using he
    · rintro ⟨t,hlo,hhi,he⟩
      refine ⟨boundary 0+t,?_,?_,(post_beep t).1 he⟩
      · have hh := relativeBoundary_offset i
        omega
      · have hh := relativeBoundary_offset (i+1)
        omega
  event_unique := by
    intro i j k hjlo hjhi hklo hkhi hj hk
    have h1 := relativeBoundary_offset i
    have h2 := relativeBoundary_offset (i+1)
    have hu := boundary_event_unique i (boundary 0+j) (boundary 0+k)
      (by omega) (by omega) (by omega) (by omega) ((post_beep j).1 hj) ((post_beep k).1 hk)
    omega

end Shared.PNP.Record285.AlignedPhysical
