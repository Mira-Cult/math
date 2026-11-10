import PASoundness.M236OccurrenceGraphConverse
import PASoundness.M236Observer
/-! Ordered-output refinement from the explicit graph interpreter to M236. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open PASoundness.Observer PASoundness.UnaryCodec
open Shared.Beeping Shared.Beeping.Machines

/-- Off the reachable graph, missing rows stutter silently. Reachability of
this fallback is not assumed; the refinement proves it is never used. -/
def graphSystem : WordEventSystem GraphState Bool where
  initial := graphInitial
  step := fun s => match graphNext s with
    | some (events, next) => (next, events)
    | none => (s, [])

theorem graphSystem_run (n : Nat) : graphSystem.run n = (states n).val.graphState := by
  induction n with
  | zero => exact initial_graph_state.symm
  | succ n ih =>
    rw [WordEventSystem.run_succ, ih]
    simp only [graphSystem, selected_graphNext]

theorem graphSystem_prefix (n : Nat) : graphSystem.prefixWord n = output n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [WordEventSystem.prefix_succ, ih, graphSystem_run]
    simp only [graphSystem, selected_graphNext, output]

/-- The literal 236-state blank-start machine refines the executable retained
graph interpreter at strictly increasing physical times. -/
noncomputable def graphRefinement :
    WordRefinement graphSystem (machineWordSystem machine machineLabels) where
  Rel := fun g c => ∃ s : Snapshot, Good s ∧ s.graphState = g ∧ mapConfig s.config = c
  boundary := fun n => 89821408 + elapsed n
  progress := by
    intro n
    simpa only [Nat.succ_eq_add_one] using
      Nat.add_lt_add_left (elapsed_strict (Nat.lt_succ_self n)) 89821408
  related := by
    intro n
    refine ⟨(states n).val, (states n).property, ?_, ?_⟩
    · exact (graphSystem_run n).symm
    · exact (selected_coherent_execution.2.2 n).2.2.1
  prefix_eq := by
    intro n
    rw [(selected_coherent_execution.2.2 n).2.2.2, graphSystem_prefix]

/-- Identical complete ordered output, whether that output is finite or infinite. -/
theorem graph_sameOutput : SameOutput graphSystem (machineWordSystem machine machineLabels) :=
  graphRefinement.sameOutput

/-- The fixed observer's receipt and error guards agree for the graph and the
actual selected machine. Frame progress is a separate obligation. -/
theorem graph_sameReceipts :
    SameReceipts (wordDecodedEvents graphSystem)
      (wordDecodedEvents (machineWordSystem machine machineLabels)) :=
  sameOutput_sameReceipts graph_sameOutput

theorem graph_accept_iff :
    M236Observer.Accept (wordDecodedEvents graphSystem) ↔
      M236Observer.Accept (wordDecodedEvents (machineWordSystem machine machineLabels)) :=
  M236Observer.accept_preserved graph_sameReceipts
/-- A completed-frame boundary in the graph transfers to one at arbitrarily
late physical times; no converse is claimed here. -/
theorem graph_frameProgress_forward
    (h : M236Observer.FrameProgress graphSystem) :
    M236Observer.FrameProgress (machineWordSystem machine machineLabels) := by
  intro t
  obtain ⟨k, hk, hcursor, hones⟩ := h t
  refine ⟨89821408 + elapsed k, ?_, ?_, ?_⟩
  · have hl := elapsed_lower k
    omega
  · rw [(selected_coherent_execution.2.2 k).2.2.2, ← graphSystem_prefix k]
    exact hcursor
  · rw [(selected_coherent_execution.2.2 k).2.2.2, ← graphSystem_prefix k]
    exact hones

/-- A frame-progressing accepted graph produces an accepted physical trace. -/
theorem graph_traceAccept_implies_physical
    (h : M236Observer.TraceAccept graphSystem) :
    M236Observer.TraceAccept (machineWordSystem machine machineLabels) :=
  ⟨graph_accept_iff.mp h.1, graph_frameProgress_forward h.2⟩

end PASoundness.M236.OccurrenceGraph
