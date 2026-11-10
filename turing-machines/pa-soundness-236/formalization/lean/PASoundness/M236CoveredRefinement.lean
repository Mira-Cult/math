import PASoundness.M236CoveredStages

/-! Reusable source-to-graph and source-to-machine refinement infrastructure.
The present `CoveredStage` predicate is provably not universal: stage 12 is a
bounded atomic case excluded by its current disjuncts. Consequently the
covered-stage specializations below are vacuous until the coverage predicate is
extended; the generic frame-block interface remains useful for that work. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

/-- Clean scheduler entries relate a source stage to a graph state; the finite
reserve is kept existential because each completed frame may extend it. -/
def CleanStage (stage : Nat) (state : GraphState) : Prop :=
  ∃ reserve, state = cfg 0 BlankFirst.zeros stage 0 0 reserve

/-- A sufficient global source-to-graph obligation: every clean stage and every
finite reserve has a positive, correct frame block. -/
def StageFrameBlocks : Prop :=
  ∀ stage reserve, ∃ duration nextReserve, 0 < duration ∧
    graphSystem.Block (cfg 0 BlankFirst.zeros stage 0 0 reserve) duration
      (cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve)
      ((Source.source M236Game.selectedValue).step stage).2

/-- A duration chosen from the proved positive finite block for each stage and
reserve. -/
noncomputable def frameDuration (blocks : StageFrameBlocks)
    (stage : Nat) (reserve : List Nat) : Nat :=
  Classical.choose (blocks stage reserve)

theorem frameDuration_spec (blocks : StageFrameBlocks)
    (stage : Nat) (reserve : List Nat) :
    ∃ nextReserve, 0 < frameDuration blocks stage reserve ∧
      graphSystem.Block (cfg 0 BlankFirst.zeros stage 0 0 reserve)
        (frameDuration blocks stage reserve)
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve)
        ((Source.source M236Game.selectedValue).step stage).2 := by
  exact Classical.choose_spec (blocks stage reserve)

/-- The actual graph starts clean and silent. Each source frame is represented
by one of the supplied positive-duration graph blocks. -/
noncomputable def schedulerSimulation (blocks : StageFrameBlocks) :
    SegmentSimulation (Source.source M236Game.selectedValue) graphSystem where
  Rel := CleanStage
  startup := 0
  initial := by
    refine ⟨BlankFirst.reserve, ?_⟩
    exact initial_copy_entry
  startup_silent := rfl
  duration := fun stage state => frameDuration blocks stage state.reserve
  positive := by
    intro stage state h
    rcases h with ⟨reserve, rfl⟩
    exact (frameDuration_spec blocks stage reserve).choose_spec.1
  next := by
    intro stage state h
    rcases h with ⟨reserve, rfl⟩
    obtain ⟨nextReserve, _, block⟩ := frameDuration_spec blocks stage reserve
    exact ⟨nextReserve, block.endpoint⟩
  word_eq := by
    intro stage state h
    rcases h with ⟨reserve, rfl⟩
    obtain ⟨_, _, block⟩ := frameDuration_spec blocks stage reserve
    exact block.output

/-- A global family of exact frame blocks yields coherent strictly increasing,
cofinal source-to-graph boundaries with exact ordered prefix equality. -/
noncomputable def schedulerGraphRefinement (blocks : StageFrameBlocks) :
    WordRefinement (Source.source M236Game.selectedValue) graphSystem :=
  (schedulerSimulation blocks).toRefinement

/-- Composition with the established graph-to-machine refinement preserves all
ordered output, including arbitrary late physical output. -/
noncomputable def schedulerMachineRefinement (blocks : StageFrameBlocks) :
    WordRefinement (Source.source M236Game.selectedValue)
      (machineWordSystem machine machineLabels) :=
  (schedulerGraphRefinement blocks).trans graphRefinement

theorem scheduler_graph_cofinal (blocks : StageFrameBlocks) (t : Nat) :
    ∃ i, t < (schedulerGraphRefinement blocks).boundary i :=
  (schedulerGraphRefinement blocks).cofinal t

theorem scheduler_machine_cofinal (blocks : StageFrameBlocks) (t : Nat) :
    ∃ i, t < (schedulerMachineRefinement blocks).boundary i :=
  (schedulerMachineRefinement blocks).cofinal t

theorem scheduler_graph_sameOutput (blocks : StageFrameBlocks) :
    SameOutput (Source.source M236Game.selectedValue) graphSystem :=
  (schedulerGraphRefinement blocks).sameOutput

theorem scheduler_machine_sameOutput (blocks : StageFrameBlocks) :
    SameOutput (Source.source M236Game.selectedValue) (machineWordSystem machine machineLabels) :=
  (schedulerMachineRefinement blocks).sameOutput

/-- The existing frame cases would furnish the required blocks if all stages
were covered. That hypothesis is currently false, as shown below. -/
theorem covered_stage_blocks (coverage : ∀ stage, CoveredStage stage) : StageFrameBlocks := by
  intro stage reserve
  exact covered_stage_block stage reserve (coverage stage)

/-- This specialization is currently vacuous: see `not_all_stages_covered`. -/
noncomputable def coveredGraphRefinement (coverage : ∀ stage, CoveredStage stage) :
    WordRefinement (Source.source M236Game.selectedValue) graphSystem :=
  schedulerGraphRefinement (covered_stage_blocks coverage)

/-- This specialization is currently vacuous: see `not_all_stages_covered`. -/
noncomputable def coveredMachineRefinement (coverage : ∀ stage, CoveredStage stage) :
    WordRefinement (Source.source M236Game.selectedValue)
      (machineWordSystem machine machineLabels) :=
  schedulerMachineRefinement (covered_stage_blocks coverage)

theorem covered_graph_cofinal (coverage : ∀ stage, CoveredStage stage) (t : Nat) :
    ∃ i, t < (coveredGraphRefinement coverage).boundary i :=
  (coveredGraphRefinement coverage).cofinal t

theorem covered_machine_cofinal (coverage : ∀ stage, CoveredStage stage) (t : Nat) :
    ∃ i, t < (coveredMachineRefinement coverage).boundary i :=
  (coveredMachineRefinement coverage).cofinal t

theorem covered_graph_sameOutput (coverage : ∀ stage, CoveredStage stage) :
    SameOutput (Source.source M236Game.selectedValue) graphSystem :=
  (coveredGraphRefinement coverage).sameOutput

theorem covered_machine_sameOutput (coverage : ∀ stage, CoveredStage stage) :
    SameOutput (Source.source M236Game.selectedValue) (machineWordSystem machine machineLabels) :=
  (coveredMachineRefinement coverage).sameOutput

/-- The current coverage cases do not include this concrete bounded atomic
stage. Therefore the universal coverage premise remains false until the
predicate is extended with additional proved cases. -/
theorem stage_twelve_not_covered : ¬ CoveredStage 12 := by
  intro h
  rcases h with h | h | ⟨count, extra, h, hover⟩ | ⟨count, h, hb, hn⟩
  · simp [Cantor.unpair, Cantor.unpairAux] at h
  · simp [Cantor.unpair, Cantor.unpairAux] at h
  · have hc : count = 1 := by
      simp [Cantor.unpair, Cantor.unpairAux] at h
      omega
    subst count
    simp [stageSecondCoordinate, stageRemaining, Cantor.unpair, Cantor.unpairAux] at hover
  · have hc : count = 1 := by
      simp [Cantor.unpair, Cantor.unpairAux] at h
      omega
    subst count
    simp [stageFormula, stageChallenge, stageSecondCoordinate, stageRemaining,
      stageRemainingMoves, Schedule.decodeCoordinates, NonatomicMoves,
      Cantor.unpair, Cantor.unpairAux] at hn

theorem not_all_stages_covered : ¬ (∀ stage, CoveredStage stage) := by
  intro coverage
  exact stage_twelve_not_covered (coverage 12)

end PASoundness.M236.OccurrenceGraph
