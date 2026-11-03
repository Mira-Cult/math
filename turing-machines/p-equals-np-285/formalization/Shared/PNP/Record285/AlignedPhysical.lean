import Shared.PNP.Record285.ZeroBoundary
import Shared.PNP.Record285.ProducerFullBoundary

/-! Align every search-controller action boundary with a literal full-tape
boundary through the actual finite compiler passes. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.AlignedPhysical
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarCoreGraph
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.IncrementSelector
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.GrammarCoreZero

noncomputable def logicalIndex (i : Nat) : Nat :=
  Classical.choose (ZeroBoundary.source_boundary_is_producer_boundary i)

noncomputable def producerIndex (i : Nat) : Nat :=
  Classical.choose (Classical.choose_spec (ZeroBoundary.source_boundary_is_producer_boundary i))

theorem alignment (i : Nat) :
    let r := SourceControllerSimulation.simulation.toEventRefinement
    let n := 1+r.boundary i
    let j := logicalIndex i
    let m := producerIndex i
    n = ExpansionBoundary.exactRefinement.boundary j ∧
    acceptedCoalescing.boundary j = ZeroBoundary.exactRefinement.boundary m ∧
    SourceControllerSimulation.Rel (Source.controller.run i)
      (SourceControllerSimulation.shiftedGraph.run (r.boundary i)) ∧
    RegisterProjection.Rel RegisterProjection.lift expandedRows
      ((system RegisterProjection.originalRows).run n) ((system expandedRows).run n) ∧
    ExpansionRel logicalRows expansionMap ((system logicalRows).run j) ((system expandedRows).run n) ∧
    CoalescedRel logicalRows logicalMasks inputRows masks classMap graphMap
      ((system logicalRows).run j) ((coreSystem inputRows).run (acceptedCoalescing.boundary j)) ∧
    RewriteRel inputRows producerRows masks retainedMap ((coreSystem producerRows).run m)
      ((coreSystem inputRows).run (acceptedCoalescing.boundary j)) := by
  exact Classical.choose_spec (Classical.choose_spec (ZeroBoundary.source_boundary_is_producer_boundary i))

/-- A semantic relation from a source search state to the entire literal
configuration. All graph banks and rewrite phases are existentially recorded;
the final predicate fixes the whole tape, absolute head and control word. -/
def Rel (s : Source.SearchState) (physical : Shared.Beeping.Machines.Config 285) : Prop :=
  ∃ (original expanded logical : OwnershipCore.State) (input producer : CoreState)
    (g : GrammarControlGraph.State) (p : GrammarPure.State)
    (word : List Bool) (marker : Bool) (origin : Int) (leftTail gap : Nat),
    SourceControllerSimulation.Rel s original ∧
    RegisterProjection.Rel RegisterProjection.lift expandedRows original expanded ∧
    ExpansionRel logicalRows expansionMap logical expanded ∧
    CoalescedRel logicalRows logicalMasks inputRows masks classMap graphMap logical input ∧
    RewriteRel inputRows producerRows masks retainedMap producer input ∧
    CoreRel producerRows producerPositions producer g ∧
    g.fields = p.fields ∧ p.control = word++[marker] ∧ 163 ≤ gap ∧
    PhysicalNumeric.Rel
      (denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft [false])
        origin leftTail (runPattern false gap true (2*blocksBits p.fields 0))) physical

noncomputable def boundary (i : Nat) : Nat := ProducerFullBoundary.boundary (producerIndex i)

theorem related_at_boundary (i : Nat) :
    Rel (Source.controller.run i) (Shared.PNP.Record285.machine.system.run (boundary i)) := by
  have ha := alignment i
  let r := SourceControllerSimulation.simulation.toEventRefinement
  let n := 1+r.boundary i
  let j := logicalIndex i
  let m := producerIndex i
  change n = ExpansionBoundary.exactRefinement.boundary j ∧
    acceptedCoalescing.boundary j = ZeroBoundary.exactRefinement.boundary m ∧
    SourceControllerSimulation.Rel (Source.controller.run i)
      (SourceControllerSimulation.shiftedGraph.run (r.boundary i)) ∧
    RegisterProjection.Rel RegisterProjection.lift expandedRows
      ((system RegisterProjection.originalRows).run n) ((system expandedRows).run n) ∧
    ExpansionRel logicalRows expansionMap ((system logicalRows).run j) ((system expandedRows).run n) ∧
    CoalescedRel logicalRows logicalMasks inputRows masks classMap graphMap
      ((system logicalRows).run j) ((coreSystem inputRows).run (acceptedCoalescing.boundary j)) ∧
    RewriteRel inputRows producerRows masks retainedMap ((coreSystem producerRows).run m)
      ((coreSystem inputRows).run (acceptedCoalescing.boundary j)) at ha
  obtain ⟨g,p,word,marker,origin,leftTail,gap,hcore,hfields,hcontrol,hgap,htape⟩ :=
    ProducerFullBoundary.boundary_full_tape m
  have hshift : SourceControllerSimulation.shiftedGraph.run (r.boundary i) =
      (system RegisterProjection.originalRows).run n := by
    simpa [n] using SourceControllerSimulation.shifted_run (r.boundary i)
  rw [hshift] at ha
  exact ⟨(system RegisterProjection.originalRows).run n,(system expandedRows).run n,
    (system logicalRows).run j,(coreSystem inputRows).run (acceptedCoalescing.boundary j),
    (coreSystem producerRows).run m,g,p,word,marker,origin,leftTail,gap,
    ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2.1,ha.2.2.2.2.2.1,ha.2.2.2.2.2.2,hcore,
    hfields,hcontrol,hgap,htape⟩

/-- All source actions have distinct, strictly advancing physical boundaries. -/
theorem logicalIndex_strict {i j : Nat} (hij : i < j) : logicalIndex i < logicalIndex j := by
  have hi := (alignment i).1
  have hj := (alignment j).1
  have hs := SourceControllerSimulation.simulation.toEventRefinement.boundary_strict hij
  by_cases h : logicalIndex i < logicalIndex j
  · exact h
  · have hm := ExpansionBoundary.exactRefinement.boundary_mono (show logicalIndex j ≤ logicalIndex i by omega)
    omega

theorem producerIndex_strict {i j : Nat} (hij : i < j) : producerIndex i < producerIndex j := by
  have hi := (alignment i).2.1
  have hj := (alignment j).2.1
  have hs := acceptedCoalescing.boundary_strict (logicalIndex_strict hij)
  by_cases h : producerIndex i < producerIndex j
  · exact h
  · have hm := ZeroBoundary.exactRefinement.boundary_mono (show producerIndex j ≤ producerIndex i by omega)
    omega

theorem boundary_strict {i j : Nat} (hij : i < j) : boundary i < boundary j :=
  ProducerFullBoundary.boundary_strict (producerIndex_strict hij)

theorem boundary_unbounded (t : Nat) : ∃ i, t < boundary i := by
  have hge (i : Nat) : i ≤ boundary i := by
    induction i with
    | zero => omega
    | succ i ih =>
      have hs := boundary_strict (show i < i+1 by omega)
      omega
  exact ⟨t+1,by have h := hge (t+1); omega⟩

end Shared.PNP.Record285.AlignedPhysical
