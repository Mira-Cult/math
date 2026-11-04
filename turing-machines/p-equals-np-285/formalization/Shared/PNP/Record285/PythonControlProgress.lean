import Shared.PNP.Record285.PythonControlSimulation

/-! The concrete typed run never reaches an interpreter fault or return sink.
The cofinal positive-progress refinement supplies a later live boundary. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlProgress
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSimulationLocal
open Shared.PNP.Record285.PythonControlSimulation

theorem related_live (q : SearchState) (x : Status) (h : Rel q x) :
    ∃ c, x=.live c := by
  rcases h with ⟨hq,hx⟩ | ⟨s,hprog,hexp,hphase⟩
  · subst x
    exact ⟨_,rfl⟩
  · cases hp : q.phase with
    | begin =>
      simp only [hp] at hphase
      subst x
      exact ⟨_,rfl⟩
    | compare =>
      simp only [hp] at hphase
      rcases hphase with ⟨hx,_,_,_,_⟩
      subst x
      exact ⟨_,rfl⟩

theorem fault_advance (n : Nat) : mainSystem.advance .fault n = .fault := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (step code (mainSystem.advance .fault n)).1 = .fault
    rw [ih]
    rfl

theorem return_advance (value n : Nat) :
    mainSystem.advance (.returned value) n = .returned value := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (step code (mainSystem.advance (.returned value) n)).1 = .returned value
    rw [ih]
    rfl

theorem main_runs_live (t : Nat) : ∃ c, mainSystem.run t = .live c := by
  obtain ⟨i,hi⟩ := refinement.boundaries_unbounded t
  obtain ⟨c,hc⟩ := related_live _ _ (refinement.related i)
  have hsum : t+(refinement.boundary i-t)=refinement.boundary i := by omega
  have hrun := mainSystem.run_add t (refinement.boundary i-t)
  rw [hsum] at hrun
  cases hx : mainSystem.run t with
  | live current => exact ⟨current,rfl⟩
  | fault =>
    rw [hx,fault_advance] at hrun
    rw [hrun] at hc
    contradiction
  | returned value =>
    rw [hx,return_advance] at hrun
    rw [hrun] at hc
    contradiction

end Shared.PNP.Record285.PythonControlProgress
