import Shared.PNP.Record285.PythonControlSimulationCompare

/-! Positive-duration, event-exact simulation of the verified source
controller by the typed interpreter of the frozen listing. This does not
claim a verified CPython parser or Python implementation semantics. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlSimulation
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip (pySystem)
open Shared.PNP.Record285.PythonControlEvaluator (sameAdvance sameBeep)
open Shared.PNP.Record285.PythonControlLocal
open Shared.PNP.Record285.PythonControlSimulationLocal
open Shared.PNP.Record285.PythonControlSimulationCompare

theorem segment_exists (q : SearchState) (x : Status) (h : Rel q x) : StepWitness q x := by
  rcases h with ⟨hq,hx⟩ | ⟨s,hprog,hexp,hphase⟩
  · subst q
    subst x
    exact startup_sim
  · cases hp : q.phase with
    | begin =>
      simp only [hp] at hphase
      subst x
      exact begin_sim q s hp hprog hexp
    | compare =>
      simp only [hp] at hphase
      obtain ⟨hx,hname,hradix,hremaining,hpos⟩ := hphase
      subst x
      exact compare_sim q s hp hprog hexp hname hradix hremaining hpos

noncomputable def duration (q : SearchState) (x : Status) : Nat := by
  classical
  exact if h : Rel q x then Classical.choose (segment_exists q x h) else 1

theorem duration_spec (q : SearchState) (x : Status) (h : Rel q x) :
    ∃ y, 0 < duration q x ∧ Local x y (duration q x) (controllerStep q).2 ∧
      Rel (controllerStep q).1 y := by
  classical
  have hd : duration q x = Classical.choose (segment_exists q x h) := by simp [duration,h]
  rw [hd]
  exact Classical.choose_spec (segment_exists q x h)

noncomputable def simulation : SegmentSimulation controller mainSystem where
  Rel := Rel
  initial := Or.inl ⟨rfl,rfl⟩
  duration := duration
  positive := by
    intro q x h
    obtain ⟨y,hpos,hl,hr⟩ := duration_spec q x h
    exact hpos
  next := by
    intro q x h
    obtain ⟨y,hpos,hl,hr⟩ := duration_spec q x h
    change Rel (controllerStep q).1 (mainSystem.advance x (duration q x))
    rw [sameAdvance mainSystem pySystem rfl,hl.1]
    exact hr
  event_iff := by
    intro q x h
    obtain ⟨y,hpos,hl,hr⟩ := duration_spec q x h
    change ((controllerStep q).2 = true ↔
      ∃ j, j < duration q x ∧ mainSystem.BeepFrom x j)
    constructor
    · intro he
      obtain ⟨j,hj,hb⟩ := hl.2.1.1 he
      exact ⟨j,hj,(sameBeep mainSystem pySystem rfl x j).2 hb⟩
    · rintro ⟨j,hj,hb⟩
      exact hl.2.1.2 ⟨j,hj,(sameBeep mainSystem pySystem rfl x j).1 hb⟩
  event_unique := by
    intro q x h j k hj hk hjb hkb
    obtain ⟨y,hpos,hl,hr⟩ := duration_spec q x h
    exact hl.2.2 j k hj hk (sameBeep mainSystem pySystem rfl x j |>.1 hjb)
      (sameBeep mainSystem pySystem rfl x k |>.1 hkb)

noncomputable def refinement : EventRefinement controller mainSystem := simulation.toEventRefinement

theorem eventuallySilent_iff : controller.EventuallySilent ↔ mainSystem.EventuallySilent :=
  refinement.eventuallySilent_iff

theorem infinitelyMany_iff : controller.InfinitelyManyBeeps ↔ mainSystem.InfinitelyManyBeeps :=
  refinement.infinitelyManyBeeps_iff

end Shared.PNP.Record285.PythonControlSimulation
