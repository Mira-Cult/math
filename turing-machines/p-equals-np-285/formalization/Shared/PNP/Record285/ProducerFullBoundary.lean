import Shared.PNP.Record285.ProjectionEndpoint
import Shared.PNP.Record285.SourceControllerSimulation

/-! Expose the full literal tape carried by the already proved producer-core
refinement, at its cofinal action boundaries. This does not yet connect those
boundaries directly to the higher-level search controller. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.ProducerFullBoundary
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarCoreGraph
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.IncrementSelector

noncomputable def boundary (i : Nat) : Nat :=
  89806142 + producerPhysicalRefinement.boundary i

theorem boundary_strict {i j : Nat} (h : i < j) : boundary i < boundary j := by
  have hh := producerPhysicalRefinement.boundary_strict h
  simp only [boundary]
  omega

theorem boundary_unbounded (t : Nat) : ∃ i, t < boundary i := by
  obtain ⟨i,hi⟩ := producerPhysicalRefinement.boundaries_unbounded t
  exact ⟨i,by simp only [boundary]; omega⟩

/-- At every producer action boundary the complete physical two-way tape,
absolute head, control path and complete register bank have one common
representation, starting from the actual blank-start run. The graph-to-pure
relation includes the correspondence between the graph program counter and
the represented control word. -/
theorem boundary_full_tape (i : Nat) :
    ∃ (g : GrammarControlGraph.State) (p : GrammarPure.State)
      (word : List Bool) (marker : Bool) (origin : Int) (leftTail gap : Nat),
      CoreRel producerRows producerPositions ((coreSystem producerRows).run i) g ∧
      GrammarControlGraph.Related g p ∧ p.control = word++[marker] ∧ 163 ≤ gap ∧
      PhysicalNumeric.Rel
        (denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft [false])
          origin leftTail (runPattern false gap true (2*blocksBits p.fields 0)))
        (Shared.PNP.Record285.machine.system.run (boundary i)) := by
  have h := producerPhysicalRefinement.related i
  change ∃ g, CoreRel producerRows producerPositions ((coreSystem producerRows).run i) g ∧
    ∃ p, GrammarControlGraph.Related g p ∧
      ∃ s, GrammarPure.Related p s ∧
        s.physical = GrammarOperationalRun.physicalSystem.run (producerPhysicalRefinement.boundary i) at h
  obtain ⟨g,hcore,p,hgp,s,hps,hphysical⟩ := h
  obtain ⟨hfields,word,marker,origin,leftTail,gap,hcontrol,hgap,htape⟩ := hps
  have hrun : GrammarOperationalRun.physicalSystem.run (producerPhysicalRefinement.boundary i) =
      Shared.PNP.Record285.machine.system.run (boundary i) := by
    exact restarted_run_offset Shared.PNP.Record285.machine.system 89806142 _
  rw [hphysical,hrun] at htape
  exact ⟨g,p,word,marker,origin,leftTail,gap,hcore,hgp,hcontrol,hgap,htape⟩

/-- At the corresponding pre-zero-elimination graph boundary, the checked
rewrite relates the complete register list to the same complete physical
tape. The two boundary maps are cofinal in their respective executions. -/
theorem input_graph_full_tape (i : Nat) :
    ∃ (g : GrammarControlGraph.State) (p : GrammarPure.State)
      (word : List Bool) (marker : Bool) (origin : Int) (leftTail gap : Nat),
      GrammarCoreZero.RewriteRel GrammarCoreZero.inputRows producerRows GrammarCoreZero.masks
        GrammarCoreZero.retainedMap ((coreSystem producerRows).run i)
          ((coreSystem GrammarCoreZero.inputRows).run (GrammarCoreZero.acceptedRewrite.boundary i)) ∧
      CoreRel producerRows producerPositions ((coreSystem producerRows).run i) g ∧
      ((coreSystem GrammarCoreZero.inputRows).run (GrammarCoreZero.acceptedRewrite.boundary i)).fields = p.fields ∧
      p.control = word++[marker] ∧ 163 ≤ gap ∧
      PhysicalNumeric.Rel
        (denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft [false])
          origin leftTail (runPattern false gap true (2*blocksBits p.fields 0)))
        (Shared.PNP.Record285.machine.system.run (boundary i)) := by
  obtain ⟨g,p,word,marker,origin,leftTail,gap,hcore,hfields,hcontrol,hgap,htape⟩ := boundary_full_tape i
  have hr := GrammarCoreZero.acceptedRewrite.related i
  change GrammarCoreZero.RewriteRel GrammarCoreZero.inputRows producerRows GrammarCoreZero.masks
    GrammarCoreZero.retainedMap ((coreSystem producerRows).run i)
      ((coreSystem GrammarCoreZero.inputRows).run (GrammarCoreZero.acceptedRewrite.boundary i)) at hr
  have heq := hr.2.2.1
  exact ⟨g,p,word,marker,origin,leftTail,gap,hr,hcore,heq.symm.trans (hcore.2.1.trans hfields.1),
    hcontrol,hgap,htape⟩

/-- The same pre-elimination boundary lies inside one finite logical-graph
segment. The exact intermediate input-graph state is specified, including
its whole register bank; the offset is strictly inside that segment. -/
theorem logical_phase_at_input_boundary (i : Nat) :
    ∃ j k,
      GrammarCoreZero.acceptedRewrite.boundary i = OwnershipCore.acceptedCoalescing.boundary j+k ∧
      k < OwnershipCore.acceptedCoalescing.boundary (j+1)-OwnershipCore.acceptedCoalescing.boundary j ∧
      OwnershipCore.CoalescedRel OwnershipCore.logicalRows OwnershipCore.logicalMasks
        GrammarCoreZero.inputRows GrammarCoreZero.masks OwnershipCore.classMap OwnershipCore.graphMap
        ((OwnershipCore.system OwnershipCore.logicalRows).run j)
        ((coreSystem GrammarCoreZero.inputRows).run (OwnershipCore.acceptedCoalescing.boundary j)) ∧
      ((coreSystem GrammarCoreZero.inputRows).run (GrammarCoreZero.acceptedRewrite.boundary i)) =
        (coreSystem GrammarCoreZero.inputRows).advance
          ((coreSystem GrammarCoreZero.inputRows).run (OwnershipCore.acceptedCoalescing.boundary j)) k := by
  let n := GrammarCoreZero.acceptedRewrite.boundary i
  let r := OwnershipCore.acceptedCoalescing
  obtain ⟨j,hlo,hhi⟩ := r.covers n
  let k := n-r.boundary j
  have heq : n = r.boundary j+k := by dsimp [k]; omega
  have hk : k < r.boundary (j+1)-r.boundary j := by dsimp [k]; omega
  have hrel := r.related j
  change OwnershipCore.CoalescedRel OwnershipCore.logicalRows OwnershipCore.logicalMasks
    GrammarCoreZero.inputRows GrammarCoreZero.masks OwnershipCore.classMap OwnershipCore.graphMap
    ((OwnershipCore.system OwnershipCore.logicalRows).run j)
    ((coreSystem GrammarCoreZero.inputRows).run (r.boundary j)) at hrel
  refine ⟨j,k,heq,hk,hrel,?_⟩
  change (coreSystem GrammarCoreZero.inputRows).run n = _
  rw [heq,EventSystem.run_add]

/-- At each logical-graph action boundary, the expanded graph and the
pre-projection graph agree on every retained register; omitted registers are
zero. This supplies the exact graph state on the high-level side of the
ownership contraction. -/
theorem logical_boundary_to_original (j : Nat) :
    let n := OwnershipCore.acceptedExpansion.boundary j
    OwnershipCore.ExpansionRel OwnershipCore.logicalRows OwnershipCore.expansionMap
      ((OwnershipCore.system OwnershipCore.logicalRows).run j)
      ((OwnershipCore.system OwnershipCore.expandedRows).run n) ∧
    RegisterProjection.Rel RegisterProjection.lift OwnershipCore.expandedRows
      ((OwnershipCore.system RegisterProjection.originalRows).run n)
      ((OwnershipCore.system OwnershipCore.expandedRows).run n) := by
  dsimp only
  constructor
  · exact OwnershipCore.acceptedExpansion.related j
  · exact RegisterProjection.related_run _

/-- Each whole-tape producer boundary has an identified logical action and
finite in-action offset, together with the corresponding complete expanded
and pre-projection graph states. -/
theorem full_chain_to_original_graph (i : Nat) :
    ∃ j k,
      GrammarCoreZero.acceptedRewrite.boundary i = OwnershipCore.acceptedCoalescing.boundary j+k ∧
      k < OwnershipCore.acceptedCoalescing.boundary (j+1)-OwnershipCore.acceptedCoalescing.boundary j ∧
      OwnershipCore.CoalescedRel OwnershipCore.logicalRows OwnershipCore.logicalMasks
        GrammarCoreZero.inputRows GrammarCoreZero.masks OwnershipCore.classMap OwnershipCore.graphMap
        ((OwnershipCore.system OwnershipCore.logicalRows).run j)
        ((coreSystem GrammarCoreZero.inputRows).run (OwnershipCore.acceptedCoalescing.boundary j)) ∧
      ((coreSystem GrammarCoreZero.inputRows).run (GrammarCoreZero.acceptedRewrite.boundary i)) =
        (coreSystem GrammarCoreZero.inputRows).advance
          ((coreSystem GrammarCoreZero.inputRows).run (OwnershipCore.acceptedCoalescing.boundary j)) k ∧
      let n := OwnershipCore.acceptedExpansion.boundary j
      OwnershipCore.ExpansionRel OwnershipCore.logicalRows OwnershipCore.expansionMap
        ((OwnershipCore.system OwnershipCore.logicalRows).run j)
        ((OwnershipCore.system OwnershipCore.expandedRows).run n) ∧
      RegisterProjection.Rel RegisterProjection.lift OwnershipCore.expandedRows
        ((OwnershipCore.system RegisterProjection.originalRows).run n)
        ((OwnershipCore.system OwnershipCore.expandedRows).run n) := by
  obtain ⟨j,k,heq,hk,hrel,hrun⟩ := logical_phase_at_input_boundary i
  exact ⟨j,k,heq,hk,hrel,hrun,logical_boundary_to_original j⟩

/-- Every pre-projection graph state after its initial silent row belongs to
one source-controller segment. Its exact graph configuration is obtained by
running a finite in-segment offset from a source-related boundary. -/
theorem original_graph_source_phase (n : Nat) :
    n = 0 ∨ ∃ s k,
      let r := SourceControllerSimulation.simulation.toEventRefinement
      n = 1+r.boundary s+k ∧
      k < r.boundary (s+1)-r.boundary s ∧
      SourceControllerSimulation.Rel (Source.controller.run s)
        (SourceControllerSimulation.shiftedGraph.run (r.boundary s)) ∧
      (OwnershipCore.system RegisterProjection.originalRows).run n =
        SourceControllerSimulation.shiftedGraph.advance
          (SourceControllerSimulation.shiftedGraph.run (r.boundary s)) k := by
  by_cases hz : n = 0
  · exact Or.inl hz
  · right
    let r := SourceControllerSimulation.simulation.toEventRefinement
    obtain ⟨s,hlo,hhi⟩ := r.covers (n-1)
    let k := (n-1)-r.boundary s
    have heq : n = 1+r.boundary s+k := by dsimp [k]; omega
    have hk : k < r.boundary (s+1)-r.boundary s := by dsimp [k]; omega
    refine ⟨s,k,heq,hk,r.related s,?_⟩
    have hshift : (OwnershipCore.system RegisterProjection.originalRows).run n =
        SourceControllerSimulation.shiftedGraph.run (n-1) := by
      rw [SourceControllerSimulation.shifted_run]
      congr 1
      omega
    rw [hshift]
    have hn : n-1 = r.boundary s+k := by omega
    rw [hn,EventSystem.run_add]

/-- One cofinal literal boundary, the entire represented literal tape, the
pre-elimination and logical graph phases, and the corresponding source
segment are related in one statement. The source segment may contain this
boundary at an intermediate offset; the converse alignment of every source
action with a physical segment is still a separate obligation. -/
theorem literal_boundary_source_phase_full_tape (i : Nat) :
    ∃ j k,
      GrammarCoreZero.acceptedRewrite.boundary i = OwnershipCore.acceptedCoalescing.boundary j+k ∧
      k < OwnershipCore.acceptedCoalescing.boundary (j+1)-OwnershipCore.acceptedCoalescing.boundary j ∧
      OwnershipCore.CoalescedRel OwnershipCore.logicalRows OwnershipCore.logicalMasks
        GrammarCoreZero.inputRows GrammarCoreZero.masks OwnershipCore.classMap OwnershipCore.graphMap
        ((OwnershipCore.system OwnershipCore.logicalRows).run j)
        ((coreSystem GrammarCoreZero.inputRows).run (OwnershipCore.acceptedCoalescing.boundary j)) ∧
      ((coreSystem GrammarCoreZero.inputRows).run (GrammarCoreZero.acceptedRewrite.boundary i)) =
        (coreSystem GrammarCoreZero.inputRows).advance
          ((coreSystem GrammarCoreZero.inputRows).run (OwnershipCore.acceptedCoalescing.boundary j)) k ∧
      (let n := OwnershipCore.acceptedExpansion.boundary j
       OwnershipCore.ExpansionRel OwnershipCore.logicalRows OwnershipCore.expansionMap
          ((OwnershipCore.system OwnershipCore.logicalRows).run j)
          ((OwnershipCore.system OwnershipCore.expandedRows).run n) ∧
       RegisterProjection.Rel RegisterProjection.lift OwnershipCore.expandedRows
          ((OwnershipCore.system RegisterProjection.originalRows).run n)
          ((OwnershipCore.system OwnershipCore.expandedRows).run n) ∧
       (n = 0 ∨ ∃ s k,
         let r := SourceControllerSimulation.simulation.toEventRefinement
         n = 1+r.boundary s+k ∧
         k < r.boundary (s+1)-r.boundary s ∧
         SourceControllerSimulation.Rel (Source.controller.run s)
           (SourceControllerSimulation.shiftedGraph.run (r.boundary s)) ∧
         (OwnershipCore.system RegisterProjection.originalRows).run n =
           SourceControllerSimulation.shiftedGraph.advance
             (SourceControllerSimulation.shiftedGraph.run (r.boundary s)) k)) ∧
      ∃ (g : GrammarControlGraph.State) (p : GrammarPure.State)
        (word : List Bool) (marker : Bool) (origin : Int) (leftTail gap : Nat),
        GrammarCoreZero.RewriteRel GrammarCoreZero.inputRows producerRows GrammarCoreZero.masks
          GrammarCoreZero.retainedMap ((coreSystem producerRows).run i)
          ((coreSystem GrammarCoreZero.inputRows).run (GrammarCoreZero.acceptedRewrite.boundary i)) ∧
        CoreRel producerRows producerPositions ((coreSystem producerRows).run i) g ∧
        ((coreSystem GrammarCoreZero.inputRows).run (GrammarCoreZero.acceptedRewrite.boundary i)).fields = p.fields ∧
        p.control = word++[marker] ∧ 163 ≤ gap ∧
        PhysicalNumeric.Rel
          (denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft [false])
            origin leftTail (runPattern false gap true (2*blocksBits p.fields 0)))
          (Shared.PNP.Record285.machine.system.run (boundary i)) := by
  obtain ⟨j,k,heq,hk,hrel,hrun,hexpand,hprojection⟩ := full_chain_to_original_graph i
  refine ⟨j,k,heq,hk,hrel,hrun,?_,input_graph_full_tape i⟩
  exact ⟨hexpand,hprojection,original_graph_source_phase (OwnershipCore.acceptedExpansion.boundary j)⟩

/-- The source segment indices seen by the complete-tape boundary chain are
unbounded. This rules out a physical execution whose represented boundaries
remain forever inside finitely many source actions. -/
theorem source_phases_cofinal (T : Nat) :
    ∃ i j k s l,
      T ≤ i ∧ T ≤ s ∧
      GrammarCoreZero.acceptedRewrite.boundary i = OwnershipCore.acceptedCoalescing.boundary j+k ∧
      k < OwnershipCore.acceptedCoalescing.boundary (j+1)-OwnershipCore.acceptedCoalescing.boundary j ∧
      OwnershipCore.CoalescedRel OwnershipCore.logicalRows OwnershipCore.logicalMasks
        GrammarCoreZero.inputRows GrammarCoreZero.masks OwnershipCore.classMap OwnershipCore.graphMap
        ((OwnershipCore.system OwnershipCore.logicalRows).run j)
        ((coreSystem GrammarCoreZero.inputRows).run (OwnershipCore.acceptedCoalescing.boundary j)) ∧
      ((coreSystem GrammarCoreZero.inputRows).run (GrammarCoreZero.acceptedRewrite.boundary i)) =
        (coreSystem GrammarCoreZero.inputRows).advance
          ((coreSystem GrammarCoreZero.inputRows).run (OwnershipCore.acceptedCoalescing.boundary j)) k ∧
      (let n := OwnershipCore.acceptedExpansion.boundary j
       let r := SourceControllerSimulation.simulation.toEventRefinement
       OwnershipCore.ExpansionRel OwnershipCore.logicalRows OwnershipCore.expansionMap
         ((OwnershipCore.system OwnershipCore.logicalRows).run j)
         ((OwnershipCore.system OwnershipCore.expandedRows).run n) ∧
       RegisterProjection.Rel RegisterProjection.lift OwnershipCore.expandedRows
         ((OwnershipCore.system RegisterProjection.originalRows).run n)
         ((OwnershipCore.system OwnershipCore.expandedRows).run n) ∧
       n = 1+r.boundary s+l ∧ l < r.boundary (s+1)-r.boundary s ∧
       SourceControllerSimulation.Rel (Source.controller.run s)
         (SourceControllerSimulation.shiftedGraph.run (r.boundary s)) ∧
       (OwnershipCore.system RegisterProjection.originalRows).run n =
         SourceControllerSimulation.shiftedGraph.advance
           (SourceControllerSimulation.shiftedGraph.run (r.boundary s)) l) ∧
      ∃ (g : GrammarControlGraph.State) (p : GrammarPure.State)
        (word : List Bool) (marker : Bool) (origin : Int) (leftTail gap : Nat),
        GrammarCoreZero.RewriteRel GrammarCoreZero.inputRows producerRows GrammarCoreZero.masks
          GrammarCoreZero.retainedMap ((coreSystem producerRows).run i)
          ((coreSystem GrammarCoreZero.inputRows).run (GrammarCoreZero.acceptedRewrite.boundary i)) ∧
        CoreRel producerRows producerPositions ((coreSystem producerRows).run i) g ∧
        ((coreSystem GrammarCoreZero.inputRows).run (GrammarCoreZero.acceptedRewrite.boundary i)).fields = p.fields ∧
        p.control = word++[marker] ∧ 163 ≤ gap ∧
        PhysicalNumeric.Rel
          (denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft [false])
            origin leftTail (runPattern false gap true (2*blocksBits p.fields 0)))
          (Shared.PNP.Record285.machine.system.run (boundary i)) := by
  let r := SourceControllerSimulation.simulation.toEventRefinement
  let c := OwnershipCore.acceptedCoalescing
  let e := OwnershipCore.acceptedExpansion
  let w := GrammarCoreZero.acceptedRewrite
  let J := 1+r.boundary T
  let i := c.boundary J+1
  have hi : T ≤ i := by
    have hc := c.boundary_ge J
    have hr := r.boundary_ge T
    dsimp [i,J] at *
    omega
  obtain ⟨j,k,heq,hk,hrel,hrun,hexpand,hprojection⟩ := full_chain_to_original_graph i
  have hj : J ≤ j := by
    by_cases hn : J ≤ j
    · exact hn
    · have hm := c.boundary_mono (show j+1 ≤ J by omega)
      have hp := c.progress j
      have hw := w.boundary_ge i
      change w.boundary (c.boundary J+1) = c.boundary j+k at heq
      change k < c.boundary (j+1)-c.boundary j at hk
      dsimp [i] at hw
      omega
  let n := e.boundary j
  have hn : 1+r.boundary T ≤ n := by
    have hh := e.boundary_ge j
    dsimp [n,J] at *
    omega
  have hsource := original_graph_source_phase n
  rcases hsource with hz | ⟨s,l,hstart,hl,hstate,hgraph⟩
  · omega
  have hs : T ≤ s := by
    by_cases hgood : T ≤ s
    · exact hgood
    · have hm := r.boundary_mono (show s+1 ≤ T by omega)
      have hp := r.progress s
      change n = 1+r.boundary s+l at hstart
      change l < r.boundary (s+1)-r.boundary s at hl
      omega
  refine ⟨i,j,k,s,l,hi,hs,heq,hk,hrel,hrun,?_,input_graph_full_tape i⟩
  exact ⟨hexpand,hprojection,hstart,hl,hstate,hgraph⟩

/-- Source core events are exactly the marked literal events within the
corresponding positive physical segment, with no duplicate marked event. -/
theorem boundary_event_iff (i : Nat) :
    (coreSystem producerRows).BeepAt i ↔
      ∃ t, boundary i ≤ t ∧ t < boundary (i+1) ∧ Shared.PNP.Record285.machine.system.BeepAt t := by
  rw [producerPhysicalRefinement.event_iff i]
  constructor
  · rintro ⟨t,hl,hh,he⟩
    refine ⟨89806142+t,by simp [boundary]; omega,by simp [boundary]; omega,?_⟩
    exact (restarted_beep_offset Shared.PNP.Record285.machine.system 89806142 t).1 he
  · rintro ⟨t,hl,hh,he⟩
    have ht : 89806142 ≤ t := by simp [boundary] at hl; omega
    refine ⟨t-89806142,by simp [boundary] at hl; omega,by simp [boundary] at hh; omega,?_⟩
    have h := (restarted_beep_offset Shared.PNP.Record285.machine.system 89806142 (t-89806142)).2
    apply h
    have heq : 89806142+(t-89806142)=t := by omega
    simpa [heq] using he

theorem boundary_event_unique (i t u : Nat)
    (htlo : boundary i ≤ t) (hthi : t < boundary (i+1))
    (hulo : boundary i ≤ u) (huhi : u < boundary (i+1))
    (ht : Shared.PNP.Record285.machine.system.BeepAt t)
    (hu : Shared.PNP.Record285.machine.system.BeepAt u) : t = u := by
  have ht0 : 89806142 ≤ t := by simp [boundary] at htlo; omega
  have hu0 : 89806142 ≤ u := by simp [boundary] at hulo; omega
  have ht' : GrammarOperationalRun.physicalSystem.BeepAt (t-89806142) := by
    apply (restarted_beep_offset Shared.PNP.Record285.machine.system 89806142 (t-89806142)).2
    have heq : 89806142+(t-89806142) = t := by omega
    simpa [heq] using ht
  have hu' : GrammarOperationalRun.physicalSystem.BeepAt (u-89806142) := by
    apply (restarted_beep_offset Shared.PNP.Record285.machine.system 89806142 (u-89806142)).2
    have heq : 89806142+(u-89806142) = u := by omega
    simpa [heq] using hu
  have heq := producerPhysicalRefinement.event_unique i (t-89806142) (u-89806142)
    (by simp [boundary] at htlo; omega) (by simp [boundary] at hthi; omega)
    (by simp [boundary] at hulo; omega) (by simp [boundary] at huhi; omega) ht' hu'
  omega

end Shared.PNP.Record285.ProducerFullBoundary
