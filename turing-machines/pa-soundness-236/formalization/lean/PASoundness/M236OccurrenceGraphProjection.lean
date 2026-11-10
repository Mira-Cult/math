import PASoundness.M236OccurrenceGraphWalk
/-! Project literal physical walks to the retained graph's control state. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236
open PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

structure GraphState where
  index : Nat
  registers : RegisterMachine.Bank 9
  reserve : List Nat

def Snapshot.graphState (s : Snapshot) : GraphState := ⟨s.index, s.registers, s.reserve⟩

def graphInitial : GraphState := ⟨0, BlankFirst.zeros, BlankFirst.reserve⟩

theorem initial_graph_state : initial.graphState = graphInitial := rfl

/-- Graph transition defined without tape, head, time, or physical runs. -/
def WitnessStep (a b : GraphState) (events : List Bool) : Prop :=
  ∃ edge op dest extra,
    a.index < 760 ∧ sourceRows[a.index]? = some (op, dest, extra) ∧
    GraphLabel edge op ∧ GraphBranch edge a.registers dest extra b.index ∧
    BranchEffect edge a.registers a.reserve b.registers b.reserve events

/-- A checked physical segment induces the independent graph transition. -/
theorem graph_step_projects (a b : Snapshot) (duration : Nat) (events : List Bool)
    (h : GraphStep a b duration events) : WitnessStep a.graphState b.graphState events := by
  obtain ⟨ha, hb, edge, op, dest, extra, hpath, heffect, hsuccessor, hi, hrow, hlabel, hbranch, ht, hblock⟩ := h
  exact ⟨edge, op, dest, extra, hi, hrow, hlabel, hbranch, heffect⟩

inductive WitnessWalk (start : GraphState) : Nat → List Bool → GraphState → Prop where
  | nil : WitnessWalk start 0 [] start
  | snoc {n : Nat} {priorOut events : List Bool} {before after : GraphState}
      (prior : WitnessWalk start n priorOut before) (step : WitnessStep before after events) :
      WitnessWalk start (n+1) (priorOut ++ events) after

theorem graph_walk_projects {start : Snapshot} {n elapsed : Nat} {events : List Bool}
    {finish : Snapshot} (h : GraphWalk start n elapsed events finish) :
    WitnessWalk start.graphState n events finish.graphState := by
  induction h with
  | nil => exact .nil
  | snoc prior step ih => exact .snoc ih (graph_step_projects _ _ _ _ step)

/-- Each finite projected graph prefix is realized by the literal M236 blank
run with the same event prefix and at least one physical transition per step. -/
theorem selected_blank_witness_walk (n : Nat) :
    ∃ elapsed events finish, n ≤ elapsed ∧
      WitnessWalk graphInitial n events finish.graphState ∧ Good finish ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (89821408 + elapsed) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + elapsed) = events := by
  obtain ⟨elapsed, events, finish, ht, hw, hg, hr, hp⟩ := selected_blank_graph_walk n
  exact ⟨elapsed, events, finish, ht, by simpa only [initial_graph_state] using graph_walk_projects hw, hg, hr, hp⟩
end PASoundness.M236.OccurrenceGraph
