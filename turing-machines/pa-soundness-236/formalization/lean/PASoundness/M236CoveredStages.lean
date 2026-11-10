import PASoundness.M236AlignedTimeout
import PASoundness.M236RankOneFrame

/-! Finite source/graph refinement under explicit contiguous-stage coverage. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

/-- Exactly the union of the currently proved clean-scheduler frame cases.
No claim is made here that every stage belongs to this predicate. -/
def CoveredStage (stage : Nat) : Prop :=
  (Cantor.unpair stage).1 = 0 ∨
  (Cantor.unpair stage).1 = 1 ∨
  (∃ count extra, (Cantor.unpair stage).1 = count+1 ∧
    stageSecondCoordinate stage = count+extra+1) ∨
  (∃ count, (Cantor.unpair stage).1 = count+1 ∧ stageSecondCoordinate stage ≤ count ∧
    NonatomicMoves (stageFormula stage)
      (if (stageChallenge stage).testBit (stageSecondCoordinate stage) then stageRemainingMoves stage count
       else (stageRemainingMoves stage count).drop 1))

/-- Every listed case yields exactly its selected source frame and a clean
next-stage graph boundary in positive time. -/
theorem covered_stage_block (stage : Nat) (reserve : List Nat) (covered : CoveredStage stage) :
    ∃ steps nextReserve, 0 < steps ∧
      graphSystem.Block (cfg 0 BlankFirst.zeros stage 0 0 reserve) steps
        (cfg 0 BlankFirst.zeros (stage+1) 0 0 nextReserve)
        (PASoundness.UnaryCodec.encodeFrame (Schedule.scheduledAddress stage)
          (M236Game.selectedValue (Schedule.scheduledAddress stage))) := by
  rcases covered with hrank | hrank | ⟨count, extra, hpositive, hoverflow⟩ | ⟨count, hpositive, hbudget, hpath⟩
  · exact scheduler_rank_one_frame stage reserve hrank
  · exact scheduler_rank_two_frame stage BlankFirst.zeros reserve rfl rfl rfl hrank
  · exact scheduler_overflow_frame stage count extra BlankFirst.zeros reserve rfl rfl rfl hpositive hoverflow
  · exact scheduler_bounded_nonatomic_frame stage count reserve hpositive hbudget hpath

/-- The interval is half-open: offsets `0` through `length-1` are covered. -/
def CoveredInterval (start length : Nat) : Prop := ∀ offset, offset < length → CoveredStage (start+offset)

theorem selected_source_advance (start n : Nat) :
    (Source.source M236Game.selectedValue).advance start n = start+n := by
  induction n with
  | zero => simp [WordEventSystem.advance]
  | succ n ih =>
    change ((Source.source M236Game.selectedValue).step
      ((Source.source M236Game.selectedValue).advance start n)).1 = start+(n+1)
    rw [ih]
    simp [Source.source, Nat.add_assoc]

/-- Every finite covered interval composes to one graph block with exactly the
source word, positive time per stage, and a clean endpoint. This is conditional
finite refinement, not a proof that the coverage predicate is universal. -/
theorem covered_interval_block (start length : Nat) (reserve : List Nat)
    (covered : CoveredInterval start length) :
    ∃ duration nextReserve, length ≤ duration ∧
      graphSystem.Block (cfg 0 BlankFirst.zeros start 0 0 reserve) duration
        (cfg 0 BlankFirst.zeros (start+length) 0 0 nextReserve)
        ((Source.source M236Game.selectedValue).wordFrom start length) := by
  induction length with
  | zero =>
    refine ⟨0, reserve, by omega, ?_⟩
    simpa [WordEventSystem.wordFrom] using
      WordEventSystem.Block.refl graphSystem (cfg 0 BlankFirst.zeros start 0 0 reserve)
  | succ n ih =>
    have hprefix : CoveredInterval start n := by
      intro offset hoffset
      exact covered offset (by omega)
    obtain ⟨duration, middleReserve, hd, h1⟩ := ih hprefix
    obtain ⟨steps, nextReserve, hs, h2⟩ := covered_stage_block (start+n) middleReserve (covered n (by omega))
    have h := h1.trans graphSystem h2
    refine ⟨duration+steps, nextReserve, by omega, ?_⟩
    change graphSystem.Block _ _ _
      ((Source.source M236Game.selectedValue).wordFrom start n ++
        ((Source.source M236Game.selectedValue).step
          ((Source.source M236Game.selectedValue).advance start n)).2)
    rw [selected_source_advance]
    simpa [Source.source, Nat.add_assoc] using h

/-- Every stage boundary of a covered interval is reached cleanly along the
same deterministic graph execution, with exactly its corresponding source word. -/
theorem covered_interval_clean_prefixes (start length : Nat) (reserve : List Nat)
    (covered : CoveredInterval start length) (offset : Nat) (hoffset : offset ≤ length) :
    ∃ duration nextReserve, offset ≤ duration ∧
      graphSystem.advance (cfg 0 BlankFirst.zeros start 0 0 reserve) duration =
        cfg 0 BlankFirst.zeros (start+offset) 0 0 nextReserve ∧
      graphSystem.wordFrom (cfg 0 BlankFirst.zeros start 0 0 reserve) duration =
        (Source.source M236Game.selectedValue).wordFrom start offset := by
  have hp : CoveredInterval start offset := by
    intro j hj
    exact covered j (by omega)
  obtain ⟨duration, nextReserve, hd, block⟩ := covered_interval_block start offset reserve hp
  exact ⟨duration, nextReserve, hd, block.endpoint, block.output⟩

/-- At a reachable clean graph boundary, a covered finite interval has an
exact physical output and terminates at another reachable clean boundary. -/
theorem selected_covered_interval (i start length : Nat) (reserve : List Nat)
    (covered : CoveredInterval start length)
    (h : graphSystem.run i = cfg 0 BlankFirst.zeros start 0 0 reserve) :
    ∃ duration nextReserve finish, length ≤ duration ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros (start+length) 0 0 nextReserve ∧
      graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (start+length) 0 0 nextReserve ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          (Source.source M236Game.selectedValue).wordFrom start length ∧
      (0 < length → graphRefinement.boundary i < graphRefinement.boundary (i+duration)) := by
  obtain ⟨duration, nextReserve, hd, block⟩ := covered_interval_block start length reserve covered
  have hr : graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (start+length) 0 0 nextReserve := by
    rw [WordEventSystem.run_add, h, block.endpoint]
  have hp : graphSystem.prefixWord (i+duration) = graphSystem.prefixWord i ++
      (Source.source M236Game.selectedValue).wordFrom start length := by
    rw [WordEventSystem.prefix_add, h, block.output]
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i+duration)
  refine ⟨duration, nextReserve, finish, hd, hg, hs.trans hr, hr, hconfig, ?_, ?_⟩
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, hp]
  · intro hl
    apply graphRefinement.boundary_strict
    omega

/-- If the prior physical output is already the matching source prefix, the
reached final boundary matches the whole longer source prefix. -/
theorem selected_covered_source_prefix (i start length : Nat) (reserve : List Nat)
    (covered : CoveredInterval start length)
    (h : graphSystem.run i = cfg 0 BlankFirst.zeros start 0 0 reserve)
    (hprefix : (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) =
      (Source.source M236Game.selectedValue).prefixWord start) :
    ∃ duration nextReserve finish, length ≤ duration ∧ Good finish ∧
      finish.graphState = cfg 0 BlankFirst.zeros (start+length) 0 0 nextReserve ∧
      graphSystem.run (i+duration) = cfg 0 BlankFirst.zeros (start+length) 0 0 nextReserve ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i+duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary (i+duration)) =
        (Source.source M236Game.selectedValue).prefixWord (start+length) ∧
      (0 < length → graphRefinement.boundary i < graphRefinement.boundary (i+duration)) := by
  obtain ⟨duration, nextReserve, finish, hd, hg, hs, hr, hc, hp, ht⟩ :=
    selected_covered_interval i start length reserve covered h
  refine ⟨duration, nextReserve, finish, hd, hg, hs, hr, hc, ?_, ht⟩
  rw [hprefix] at hp
  rw [WordEventSystem.prefix_add, Source.source_run]
  exact hp

/-- The first three stages all lie in the established rank-one or rank-two
cases. This finite fact does not imply coverage of later stages. -/
theorem first_three_stages_covered : CoveredInterval 0 3 := by
  intro offset hoffset
  have hcases : offset = 0 ∨ offset = 1 ∨ offset = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · left
    simp [Cantor.unpair, Cantor.unpairAux]
  · right; left
    simp [Cantor.unpair, Cantor.unpairAux]
  · left
    simpa using rank_one_stage_two

end PASoundness.M236.OccurrenceGraph
