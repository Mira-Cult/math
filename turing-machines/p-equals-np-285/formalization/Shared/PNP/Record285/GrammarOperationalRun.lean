import Shared.PNP.Record285.GrammarExactStep
import Shared.Beeping.Refinement

/-! Cofinal physical execution at exact grammar-action return boundaries. The
abstract run is selected from the literal machine and is not yet identified
with the Python source or the canonical complexity controller. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarOperationalRun
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.CleanBank
open Shared.PNP.Record285.GrammarReady
open Shared.PNP.Record285.GrammarExact

structure State where
  fields : List Nat
  physical : Shared.Beeping.Machines.Config 285
  fieldCount : 15 ≤ fields.length
  anchored : AnchoredRoot fields (-3818) 3 physical

def physicalSystem : EventSystem (Shared.Beeping.Machines.Config 285) :=
  ⟨Record285.machine.system.run 89806142,Record285.machine.step⟩

def initial : State :=
  ⟨List.replicate 1909 0,physicalSystem.initial,by simp,initial_anchored_root⟩

structure StepWitness (s : State) where
  edge : Edge
  fields : List Nat
  duration : Nat
  code : List Bool
  head : Int
  leftTail : Nat
  gap : Nat
  leaf : ZeroLeaf s.fields (-3818) 3 edge code head leftTail gap s.physical
  exactDuration : Duration edge s.fields code gap duration
  positive : 0 < duration
  update : Update edge s.fields fields
  anchored : AnchoredRoot fields (-3818) 3
    ((EventSystem.mk s.physical Record285.machine.step).run duration)
  events : Events edge s.physical duration

noncomputable def chooseStep (s : State) : StepWitness s := by
  have hn : Nonempty (StepWitness s) := by
    obtain ⟨edge,fields,duration,code,head,leftTail,gap,hleaf,hduration,hpos,hupdate,hroot,hevents⟩ :=
      anchored_exact_step s.fields (-3818) 3 s.physical s.fieldCount s.anchored (by decide)
    exact ⟨⟨edge,fields,duration,code,head,leftTail,gap,hleaf,hduration,hpos,hupdate,hroot,hevents⟩⟩
  exact Classical.choice hn

noncomputable def next (s : State) : State :=
  let w := chooseStep s
  ⟨w.fields,(EventSystem.mk s.physical Record285.machine.step).run w.duration,
    Nat.le_trans s.fieldCount (update_length w.edge s.fields w.fields w.update),w.anchored⟩

noncomputable def operationSystem : EventSystem State :=
  ⟨initial,fun s => (next s,decide ((chooseStep s).edge = .beep))⟩

theorem beepFrom_iff (physical : Shared.Beeping.Machines.Config 285) (t : Nat) :
    physicalSystem.BeepFrom physical t ↔
      (EventSystem.mk physical Record285.machine.step).BeepAt t := by
  simp only [EventSystem.BeepFrom,EventSystem.BeepAt,physicalSystem,
    Grammar.advance_eq_restarted_run]

/-- Each chosen abstract step has a positive physical segment, a grammar
leaf at its start, and no spurious or duplicated marked transitions. -/
noncomputable def simulation : SegmentSimulation operationSystem physicalSystem where
  Rel := fun s p => s.physical = p
  initial := rfl
  duration := fun s _ => (chooseStep s).duration
  positive := by intro s p h; exact (chooseStep s).positive
  next := by
    intro s p h
    subst p
    simp only [operationSystem,physicalSystem,
      Grammar.advance_eq_restarted_run]
    rfl
  event_iff := by
    intro s p h
    subst p
    let w := chooseStep s
    change (decide (w.edge = .beep) = true ↔
      ∃ j, j < w.duration ∧ physicalSystem.BeepFrom s.physical j)
    have he := w.events
    unfold Events at he
    by_cases hb : w.edge = .beep
    · simp only [hb,if_true] at he
      obtain ⟨j,hj,hbeep⟩ := he
      simp only [hb,decide_true,true_iff]
      exact ⟨j,hj,(beepFrom_iff s.physical j).2 ((hbeep j hj).2 rfl)⟩
    · simp only [hb,if_false] at he
      simp only [hb,decide_false,Bool.false_eq_true,false_iff]
      rintro ⟨j,hj,hbeep⟩
      exact he j hj ((beepFrom_iff s.physical j).1 hbeep)
  event_unique := by
    intro s p h j k hj hk hej hek
    subst p
    let w := chooseStep s
    change j < w.duration at hj
    change k < w.duration at hk
    have he := w.events
    unfold Events at he
    by_cases hb : w.edge = .beep
    · simp only [hb,if_true] at he
      obtain ⟨t,ht,hbeep⟩ := he
      have hjt := (hbeep j hj).1 ((beepFrom_iff s.physical j).1 hej)
      have hkt := (hbeep k hk).1 ((beepFrom_iff s.physical k).1 hek)
      omega
    · simp only [hb,if_false] at he
      exact False.elim (he j hj ((beepFrom_iff s.physical j).1 hej))

/-- Every literal transition after initialization lies in a finite positive
leaf-labelled segment with the event count specified by its label. -/
noncomputable def refinement : EventRefinement operationSystem physicalSystem := simulation.toEventRefinement

/-- Every abstract operation has its proved bank effect, and its next
physical boundary retains the complete anchored invariant. -/
theorem operation_step_update (n : Nat) :
    let s := operationSystem.run n
    let w := chooseStep s
    Update w.edge s.fields (operationSystem.run (n+1)).fields ∧
    AnchoredRoot (operationSystem.run (n+1)).fields (-3818) 3
      (operationSystem.run (n+1)).physical := by
  dsimp only [operationSystem,EventSystem.run_succ,next]
  exact ⟨(chooseStep _).update,(chooseStep _).anchored⟩

/-- The recorded operation is selected by the actual complete physical tape
at the beginning of the segment. -/
theorem operation_step_leaf (n : Nat) :
    let s := operationSystem.run n
    let w := chooseStep s
    ZeroLeaf s.fields (-3818) 3 w.edge w.code w.head w.leftTail w.gap s.physical :=
  (chooseStep _).leaf

/-- Each chosen boundary uses the exact checked duration for its single
literal grammar action, not an arbitrary later matching root. -/
theorem operation_step_exact_duration (n : Nat) :
    let s := operationSystem.run n
    let w := chooseStep s
    Duration w.edge s.fields w.code w.gap w.duration := (chooseStep _).exactDuration

/-- All physical transitions after the certified initialization are covered
by the cofinal positive operation segments. -/
theorem every_physical_transition_covered (t : Nat) :
    ∃ i, refinement.boundary i ≤ t ∧ t < refinement.boundary (i+1) :=
  refinement.covers t

theorem operation_eventuallySilent_iff_physical :
    operationSystem.EventuallySilent ↔ physicalSystem.EventuallySilent := refinement.eventuallySilent_iff

theorem operation_infinitelyMany_iff_physical :
    operationSystem.InfinitelyManyBeeps ↔ physicalSystem.InfinitelyManyBeeps := refinement.infinitelyManyBeeps_iff

theorem operation_eventuallySilent_iff_blank_start :
    operationSystem.EventuallySilent ↔ Record285.machine.system.EventuallySilent := by
  rw [operation_eventuallySilent_iff_physical]
  rw [EventSystem.eventuallySilent_iff_shift Record285.machine.system 89806142]
  have hshift (t : Nat) : physicalSystem.BeepAt t ↔
      Record285.machine.system.BeepAt (89806142+t) :=
    Grammar.restarted_beep_offset Record285.machine.system 89806142 t
  constructor
  · rintro ⟨T,hT⟩
    exact ⟨T,fun t ht he => hT t ht ((hshift t).2 he)⟩
  · rintro ⟨T,hT⟩
    exact ⟨T,fun t ht he => hT t ht ((hshift t).1 he)⟩

theorem operation_infinitelyMany_iff_blank_start :
    operationSystem.InfinitelyManyBeeps ↔ Record285.machine.system.InfinitelyManyBeeps := by
  rw [← EventSystem.not_eventuallySilent_iff_infinitelyMany,
      ← EventSystem.not_eventuallySilent_iff_infinitelyMany,operation_eventuallySilent_iff_blank_start]

end Shared.PNP.Record285.GrammarOperationalRun
