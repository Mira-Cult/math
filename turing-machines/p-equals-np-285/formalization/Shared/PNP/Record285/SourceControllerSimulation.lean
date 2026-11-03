import Shared.PNP.Record285.SourceControllerExit
import Shared.PNP.Record285.SourceEndpoint

/-! Progress-sensitive simulation from the source controller to the exact
pre-control graph, starting immediately after its silent initialization. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

namespace Shared.PNP.Record285.SourceControllerSimulation
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceVirtualStep
open Shared.PNP.Record285.SourceControllerExit

/-- The initial graph row increments the candidate exponent and is silent;
this shifted system begins at the following candidate-begin boundary. -/
def shiftedGraph : EventSystem State := ⟨⟨1,firstBank⟩,step originalRows⟩


theorem shifted_advance (g : State) (d : Nat) :
    shiftedGraph.advance g d = (system originalRows).advance g d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change (step originalRows (shiftedGraph.advance g d)).1 =
      (step originalRows ((system originalRows).advance g d)).1
    rw [ih]

theorem shifted_beep (g : State) (d : Nat) :
    shiftedGraph.BeepFrom g d ↔ (system originalRows).BeepFrom g d := by
  unfold EventSystem.BeepFrom
  change (step originalRows (shiftedGraph.advance g d)).2 = true ↔
    (step originalRows ((system originalRows).advance g d)).2 = true
  rw [shifted_advance]

def Rel (s : Source.SearchState) (g : State) : Prop :=
  ControllerReady g.bank ∧
    (if s.phase = .begin then s.program = g.bank 11 ∧ s.exponent = g.bank 12
      else sourceState g.bank .compare = s) ∧
    g.index = (if s.phase = .begin then 1 else 6)

theorem initial_related : Rel Source.controller.initial shiftedGraph.initial := by
  simp [Rel,ControllerReady,ReferenceReady,Source.controller,shiftedGraph,firstBank,update]

/-- Every related source transition has a finite positive graph segment,
matching its next state and containing exactly its source event, if any. -/
theorem local_segment (s : Source.SearchState) (g : State) (hr : Rel s g) :
    ∃ duration, 0 < duration ∧
      Rel (Source.controller.step s).1 (shiftedGraph.advance g duration) ∧
      ((Source.controller.step s).2 = true ↔ ∃ j, j < duration ∧ shiftedGraph.BeepFrom g j) ∧
      (∀ j k, j < duration → k < duration → shiftedGraph.BeepFrom g j → shiftedGraph.BeepFrom g k → j = k) := by
  simp only [shifted_advance,shifted_beep]
  cases g with
  | mk index bank =>
    cases hp : s.phase with
    | begin =>
      have hidx : index = 1 := by simpa [Rel,hp] using hr.2.2
      subst index
      have hfields : s.program = bank 11 ∧ s.exponent = bank 12 := by simpa [hp] using hr.2.1
      have hstep : Source.controllerStep s = Source.controllerStep (sourceState bank .begin) := by
        cases s with
        | mk program exponent n radix remaining phase =>
          cases phase with
          | begin => simp_all [Source.controllerStep,sourceState]
          | compare => simp at hp
      have hready : ControllerReady bank := hr.1
      let duration := bank 13+bank 14+bank 15+5
      have hd : 0 < duration := by dsimp [duration]; omega
      have hsegment := begin_segment bank
      change (system originalRows).advance ⟨1,bank⟩ duration = ⟨6,afterBegin bank⟩ ∧
        (system originalRows).BeepFrom ⟨1,bank⟩ 0 ∧
        (∀ j, 0 < j → j < duration → ¬ (system originalRows).BeepFrom ⟨1,bank⟩ j) ∧ _ at hsegment
      have hnew : ControllerReady (afterBegin bank) := by
        simp [ControllerReady,ReferenceReady,afterBegin,clear,update,
          hready.1.1,hready.1.2.1,hready.1.2.2,hready.2.1,hready.2.2]
      refine ⟨duration,hd,?_,?_,?_⟩
      · change Rel (Source.controllerStep s).1
          ((system originalRows).advance ⟨1,bank⟩ duration)
        rw [hstep,hsegment.1]
        have hphase : (Source.controllerStep (sourceState bank .begin)).1.phase = .compare := rfl
        simp only [Rel,hphase]
        exact ⟨hnew,afterBegin_source bank,rfl⟩
      · constructor
        · intro _; exact ⟨0,hd,hsegment.2.1⟩
        · intro _
          change (Source.controllerStep s).2 = true
          rw [hstep]
          rfl
      · intro j k hj hk hjb hkb
        have hj0 : j = 0 := by
          by_cases hz : j=0
          · exact hz
          · exact False.elim (hsegment.2.2.1 j (by omega) hj hjb)
        have hk0 : k = 0 := by
          by_cases hz : k=0
          · exact hz
          · exact False.elim (hsegment.2.2.1 k (by omega) hk hkb)
        omega
    | compare =>
      have hidx : index = 6 := by simpa [Rel,hp] using hr.2.2
      subst index
      have hf : sourceState bank .compare = s := by simpa [hp] using hr.2.1
      subst s
      have hready : ControllerReady bank := hr.1
      obtain ⟨out,d,hd,hseg,hnew,hsource,htail⟩ := controller_compare_step bank hready
      let flag := Source.mismatch (bank 11) (bank 12) (bank 13) (bank 14) (bank 15)
      change sourceState out (if flag then .begin else .compare) = _ at hsource
      have hphase : (Source.controllerStep (sourceState bank .compare)).1.phase =
          (if flag then .begin else .compare) := by
        have hh := (congrArg Source.SearchState.phase hsource).symm
        simpa [sourceState] using hh
      refine ⟨d,hd,?_,?_,?_⟩
      · change Rel (Source.controllerStep (sourceState bank .compare)).1
          ((system originalRows).advance ⟨6,bank⟩ d)
        change Silent originalRows ⟨6,bank⟩ ⟨if flag then 1 else 6,out⟩ d at hseg
        rw [hseg.1]
        unfold Rel
        rw [hphase]
        refine ⟨hnew,?_,?_⟩
        · cases hb : flag with
          | false => simpa [hb] using hsource
          | true =>
            simp only [if_true]
            constructor
            · have h := congrArg Source.SearchState.program hsource
              simpa [sourceState] using h.symm
            · have h := congrArg Source.SearchState.exponent hsource
              simpa [sourceState] using h.symm
        · cases flag <;> rfl
      · constructor
        · intro h
          change (Source.controllerStep (sourceState bank .compare)).2 = true at h
          have hc := (Source.controllerStep_beep (sourceState bank .compare)).1 h
          simp [sourceState] at hc
        · rintro ⟨j,hj,hbeep⟩
          exact False.elim (hseg.2 j hj hbeep)
      · intro j k hj hk hjb hkb
        exact False.elim (hseg.2 j hj hjb)

noncomputable def duration (s : Source.SearchState) (g : State) : Nat := by
  classical
  exact if h : Rel s g then Classical.choose (local_segment s g h) else 1

theorem duration_spec (s : Source.SearchState) (g : State) (h : Rel s g) :
    0 < duration s g ∧ Rel (Source.controller.step s).1 (shiftedGraph.advance g (duration s g)) ∧
      ((Source.controller.step s).2 = true ↔ ∃ j, j < duration s g ∧ shiftedGraph.BeepFrom g j) ∧
      (∀ j k, j < duration s g → k < duration s g → shiftedGraph.BeepFrom g j → shiftedGraph.BeepFrom g k → j = k) := by
  classical
  simpa only [duration,dif_pos h] using Classical.choose_spec (local_segment s g h)

/-- Each source step is implemented by a positive finite graph segment, with
exact event count and preserved scratch invariant. -/
noncomputable def simulation : SegmentSimulation Source.controller shiftedGraph where
  Rel := Rel
  initial := initial_related
  duration := duration
  positive := fun s g h => (duration_spec s g h).1
  next := fun s g h => (duration_spec s g h).2.1
  event_iff := fun s g h => (duration_spec s g h).2.2.1
  event_unique := fun s g h => (duration_spec s g h).2.2.2

/-- The shifted graph is exactly the original run after its first, silent
initialization transition. -/
theorem shifted_run (n : Nat) : shiftedGraph.run n = (system originalRows).run (1+n) := by
  induction n with
  | zero =>
    change (⟨1,firstBank⟩ : State) = (system originalRows).run 1
    exact first_begin_graph.symm
  | succ n ih =>
    change (step originalRows (shiftedGraph.run n)).1 =
      (step originalRows ((system originalRows).run (1+n))).1
    rw [ih]

theorem shifted_beepAt (n : Nat) :
    shiftedGraph.BeepAt n ↔ (system originalRows).BeepAt (1+n) := by
  unfold EventSystem.BeepAt
  change (step originalRows (shiftedGraph.run n)).2 = true ↔
    (step originalRows ((system originalRows).run (1+n))).2 = true
  rw [shifted_run]

theorem shifted_eventuallySilent_iff :
    shiftedGraph.EventuallySilent ↔ (system originalRows).EventuallySilent := by
  rw [(system originalRows).eventuallySilent_iff_shift 1]
  unfold EventSystem.EventuallySilent
  simp only [shifted_beepAt]

/-- Closed event-behavior correspondence for the Lean source controller and
the accepted literal blank-start machine. This does not assert the missing
canonical-complexity characterization or a direct full-tape relation. -/
theorem source_eventuallySilent_iff_literal :
    Source.controller.EventuallySilent ↔ Record285.machine.system.EventuallySilent :=
  simulation.toEventRefinement.eventuallySilent_iff.trans
    (shifted_eventuallySilent_iff.trans RegisterProjection.eventuallySilent_iff_blank_start)

theorem source_infinitelyMany_iff_literal :
    Source.controller.InfinitelyManyBeeps ↔ Record285.machine.system.InfinitelyManyBeeps := by
  rw [← EventSystem.not_eventuallySilent_iff_infinitelyMany,
    ← EventSystem.not_eventuallySilent_iff_infinitelyMany,source_eventuallySilent_iff_literal]

/-- The literal 285-state table is eventually silent exactly when one source
candidate passes all admissible source tests. This is not yet P = NP. -/
theorem literal_eventuallySilent_iff_goodCandidate :
    Record285.machine.system.EventuallySilent ↔
      ∃ program exponent, 0 < exponent ∧ Source.GoodCandidate program exponent :=
  source_eventuallySilent_iff_literal.symm.trans Source.eventuallySilent_iff_goodCandidate

theorem literal_infinitelyMany_iff_no_goodCandidate :
    Record285.machine.system.InfinitelyManyBeeps ↔
      ¬ ∃ program exponent, 0 < exponent ∧ Source.GoodCandidate program exponent :=
  source_infinitelyMany_iff_literal.symm.trans Source.infinitelyMany_iff_no_goodCandidate

end Shared.PNP.Record285.SourceControllerSimulation
