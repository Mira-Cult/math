import PASoundness.M236GraphFullObserver
import PASoundness.M236Reverse
import PASoundness.Peano
/-! Conditional source-to-graph composition with the exact remaining interface. -/
namespace PASoundness.M236SourceGraphBridge
open PASoundness.M236.OccurrenceGraph
open PASoundness.Observer PASoundness.UnaryCodec
open FirstOrder FirstOrder.Language
open Shared.Beeping Shared.Beeping.Machines

/-- If the repeated-address source has a positive-progress ordered-word
refinement into the retained graph, graph frame progress follows from its
complete-frame steps and cofinal refinement boundaries. -/
theorem graph_frame_progress_of_refinement (value : Address → Bool)
    (r : WordRefinement (Source.source value) graphSystem) :
    M236Observer.FrameProgress graphSystem := by
  intro t
  obtain ⟨i, hi⟩ := r.cofinal t
  refine ⟨r.boundary i, Nat.le_of_lt hi, ?_, ?_⟩
  · rw [r.prefix_eq, Source.decode_source_prefix]
    rfl
  · rw [r.prefix_eq, Source.decode_source_prefix]

/-- The fixed guarded observer is preserved by this explicit source-to-graph
refinement. It is a hypothesis, not a demonstrated producer implementation. -/
theorem graph_trace_iff_source (value : Address → Bool)
    (r : WordRefinement (Source.source value) graphSystem) :
    M236Observer.TraceAccept graphSystem ↔
      M236Observer.TraceAccept (Source.source value) := by
  change (M236Observer.Accept (wordDecodedEvents graphSystem) ∧ M236Observer.FrameProgress graphSystem) ↔
    (M236Observer.Accept (Source.events value) ∧ M236Observer.FrameProgress (Source.source value))
  rw [and_iff_left (graph_frame_progress_of_refinement value r),
      and_iff_left (M236Observer.source_frame_progress value)]
  exact (M236Observer.accept_preserved (sameOutput_sameReceipts r.sameOutput)).symm

/-- Exact remaining physical-source interface, stated as a premise. This is
not the requested unconditional M236-to-PA theorem. -/
theorem physical_iff_compact_sound_of_source_refinement
    (r : WordRefinement (Source.source M236Game.selectedValue) graphSystem) :
    M236Observer.TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      M236Reverse.CompactSound :=
  graph_traceAccept_iff.symm.trans
    ((graph_trace_iff_source M236Game.selectedValue r).trans
      M236Reverse.source_accept_iff_compact_sound)
/-- Conditional composition to genuine first-order PA. Both the selected
source-to-graph refinement and the compact-to-PA soundness bridge remain
explicit hypotheses; neither is supplied by this theorem. -/
theorem physical_iff_pa_sound_of_bridges
    (r : WordRefinement (Source.source M236Game.selectedValue) graphSystem)
    (bridge : M236Reverse.CompactSound ↔
      ∀ φ : Peano.Sentence, Peano.Proves φ → Nat ⊨ φ) :
    M236Observer.TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      ∀ φ : Peano.Sentence, Peano.Proves φ → Nat ⊨ φ :=
  (physical_iff_compact_sound_of_source_refinement r).trans bridge
end PASoundness.M236SourceGraphBridge
