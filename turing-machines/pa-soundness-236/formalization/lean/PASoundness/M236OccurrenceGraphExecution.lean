import PASoundness.M236OccurrenceGraphIndexed
/-! Graph-annotated segments on the one literal blank-start execution. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236
open PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

inductive GraphRootChain (start : Config 237) : Nat → Nat → List Bool → Config 237 → Prop where
  | nil : GraphRootChain start 0 0 [] start
  | snoc {n elapsed : Nat} {before finish : Config 237} {duration : Nat}
      {word next : List Bool} {gap nextGap : Nat}
      {registers nextRegisters : RegisterMachine.Bank 9} {reserve nextReserve : List Nat}
      {head nextHead : Int} {edge : Grammar.Edge} {out priorOut : List Bool}
      {i dest target : Nat} {op : String} {extra : Option Nat}
      (prior : GraphRootChain start n elapsed priorOut before)
      (hpath : Preparation.NamedPath Grammar.nodes 157 word edge)
      (hbefore : Canonical word gap registers reserve head [] before)
      (heffect : BranchEffect edge registers reserve nextRegisters nextReserve out)
      (hsuccessor : ControlSuccessor edge registers word next)
      (hpositive : 0 < duration)
      (hblock : (machineWordSystem raw rawLabels).Block before duration finish out)
      (hafter : Canonical next nextGap nextRegisters nextReserve nextHead [] finish)
      (hi : i < 760) (hrow : sourceRows[i]? = some (op, dest, extra))
      (hword : paths[i]? = some word) (hlabel : GraphLabel edge op)
      (hbranch : GraphBranch edge registers dest extra target)
      (hselected : target = dest ∨ extra = some target)
      (hnext : paths[target]? = some next) :
      GraphRootChain start (n + 1) (elapsed + duration) (priorOut ++ out) finish

/-- Every already-established detailed physical chain admits exact graph
annotations for each positive segment and its operation label. -/
theorem annotate_chain {start : Config 237} {n elapsed : Nat} {events : List Bool}
    {finish : Config 237} (hchain : DetailedRootChain start n elapsed events finish) :
    GraphRootChain start n elapsed events finish := by
  induction hchain with
  | nil => exact .nil
  | snoc prior hpath hbefore heffect hsuccessor hpositive hblock hafter ih =>
    obtain ⟨i, op, dest, extra, target, hi, hrow, hword, hlabel, hbranch, hselected, hnext⟩ :=
      physical_successor_graph _ _ _ _ hpath hsuccessor
    exact .snoc ih hpath hbefore heffect hsuccessor hpositive hblock hafter
      hi hrow hword hlabel hbranch hselected hnext

/-- For every finite step count the actual selected M236 blank run has an
annotated physical chain with the exact same cumulative event prefix. -/
theorem selected_blank_graph_chains (n : Nat) :
    ∃ elapsed events finish, n ≤ elapsed ∧
      GraphRootChain ((machineWordSystem raw rawLabels).run 89821408) n elapsed events finish ∧
      mapConfig finish = (machineWordSystem machine machineLabels).run (89821408 + elapsed) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + elapsed) = events ∧
      RootGood finish := by
  obtain ⟨elapsed, events, finish, ht, hchain, hrun, hprefix, hgood⟩ := selected_blank_detailed_root_chains n
  exact ⟨elapsed, events, finish, ht, annotate_chain hchain, hrun, hprefix, hgood⟩
end PASoundness.M236.OccurrenceGraph
