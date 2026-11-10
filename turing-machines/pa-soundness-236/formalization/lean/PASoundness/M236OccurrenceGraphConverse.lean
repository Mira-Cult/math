import PASoundness.M236OccurrenceGraphDeterminism
/-! Reverse finite graph simulation on the literal blank-start run. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

theorem graph_walk_run {n elapsed : Nat} {events : List Bool} {finish : Snapshot}
    (h : GraphWalk initial n elapsed events finish) :
    finish.config = (machineWordSystem raw rawLabels).run (89821408 + elapsed) ∧
    (machineWordSystem raw rawLabels).prefixWord (89821408 + elapsed) = events := by
  induction h with
  | nil => exact ⟨rfl, raw_initial_canonical_budget.2.2⟩
  | @snoc n elapsed priorOut events before after duration prior step ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hblock⟩ := step
    constructor
    · rw [← Nat.add_assoc, WordEventSystem.run_add, ← ih.1]
      exact hblock.endpoint.symm
    · rw [← Nat.add_assoc, WordEventSystem.prefix_add, ih.2, ← ih.1, hblock.output]

/-- The one coherent blank-start run follows the explicit graph interpreter. -/
theorem selected_graphNext (n : Nat) :
    graphNext (states n).val.graphState =
      some ((segment n).events, (states (n+1)).val.graphState) := by
  have hp := graph_step_projects _ _ _ _ (segment n).valid
  simpa only [next_state] using witness_step_functional _ _ _ hp

/-- Every finite witness walk is lifted to positive-time raw physical blocks. -/
theorem witness_walk_lifts {n : Nat} {events : List Bool} {finish : GraphState}
    (h : WitnessWalk graphInitial n events finish) :
    ∃ elapsed snap, n ≤ elapsed ∧ GraphWalk initial n elapsed events snap ∧
      Good snap ∧ snap.graphState = finish := by
  induction h with
  | nil => exact ⟨0, initial, by omega, .nil, initial_good, initial_graph_state⟩
  | @snoc n priorOut events before after prior step ih =>
    obtain ⟨elapsed, snap, htime, hwalk, hgood, hstate⟩ := ih
    obtain ⟨next, duration, actual, hstep, hnext⟩ := good_step snap hgood
    have projected : WitnessStep before next.graphState actual := by
      simpa only [hstate] using graph_step_projects snap next duration actual hstep
    obtain ⟨hout, hend⟩ := witness_step_deterministic before next.graphState after actual events projected step
    have hpositive : 0 < duration := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hp, _⟩ := hstep
      exact hp
    refine ⟨elapsed + duration, next, ?_, ?_, hnext, hend⟩
    · omega
    · simpa only [hout] using GraphWalk.snoc hwalk hstep

/-- Every witness walk from the canonical initial graph state is realized by
the selected literal blank-start machine with the same exact output prefix. -/
theorem selected_realizes_witness_walk {n : Nat} {events : List Bool} {finish : GraphState}
    (h : WitnessWalk graphInitial n events finish) :
    ∃ elapsed snap, n ≤ elapsed ∧ Good snap ∧ snap.graphState = finish ∧
      mapConfig snap.config = (machineWordSystem machine machineLabels).run (89821408 + elapsed) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + elapsed) = events := by
  obtain ⟨elapsed, snap, ht, hw, hg, hs⟩ := witness_walk_lifts h
  obtain ⟨hr, hp⟩ := graph_walk_run hw
  refine ⟨elapsed, snap, ht, hg, hs, ?_, ?_⟩
  · rw [hr, machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  · rw [← prefix_eq, hp]
end PASoundness.M236.OccurrenceGraph
