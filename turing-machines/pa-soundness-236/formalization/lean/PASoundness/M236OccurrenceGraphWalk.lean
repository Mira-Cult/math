import PASoundness.M236OccurrenceGraphExecution
/-! Continuous occurrence-indexed walks on the literal blank-start run. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236
open PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

theorem path_index_unique (i j : Nat) (word : List Bool)
    (hi : paths[i]? = some word) (hj : paths[j]? = some word) : i = j := by
  have hi' : Grammar.completePaths[i]? = some word := by simpa only [paths, List.getElem?_toArray] using hi
  have hj' : Grammar.completePaths[j]? = some word := by simpa only [paths, List.getElem?_toArray] using hj
  obtain ⟨ib, ie⟩ := List.getElem?_eq_some_iff.mp hi'
  obtain ⟨jb, je⟩ := List.getElem?_eq_some_iff.mp hj'
  have hn : Grammar.completePaths.Nodup := grammar_paths_nodup Grammar.nodes 158 157
  exact (List.Nodup.getElem_inj_iff hn).mp (ie.trans je.symm)

structure Snapshot where
  word : List Bool
  gap : Nat
  registers : RegisterMachine.Bank 9
  reserve : List Nat
  head : Int
  config : Config 237
  index : Nat

def Good (s : Snapshot) : Prop :=
  Grammar.LeafPath Grammar.nodes 157 s.word ∧ s.word.length + s.gap = 3819 ∧
  paths[s.index]? = some s.word ∧ Canonical s.word s.gap s.registers s.reserve s.head [] s.config

def GraphStep (a b : Snapshot) (duration : Nat) (events : List Bool) : Prop :=
  Good a ∧ Good b ∧ ∃ edge op dest extra,
    Preparation.NamedPath Grammar.nodes 157 a.word edge ∧
    BranchEffect edge a.registers a.reserve b.registers b.reserve events ∧
    ControlSuccessor edge a.registers a.word b.word ∧
    a.index < 760 ∧ sourceRows[a.index]? = some (op, dest, extra) ∧
    GraphLabel edge op ∧ GraphBranch edge a.registers dest extra b.index ∧
    0 < duration ∧ (machineWordSystem raw rawLabels).Block a.config duration b.config events

/-- One literal physical segment advances the same checked graph index. -/
theorem good_step (a : Snapshot) (ha : Good a) :
    ∃ b duration events, GraphStep a b duration events ∧ Good b := by
  obtain ⟨hleaf, hsum, hindex, hrel⟩ := ha
  have hbudget : 25 ≤ a.gap + a.word.length := by omega
  obtain ⟨edge, last, next, gap', duration, regs', reserve', events, head', finish,
    hpath, hlast, heffect, hsuccessor, hnext, hconserve, hb, hpositive, hblock, hafter, hquot⟩ :=
    canonical_physical_step_with_successor a.word a.gap a.registers a.reserve a.head [] a.config hleaf hbudget hrel
  obtain ⟨i, op, dest, extra, target, hi, hrow, hword, hlabel, hbranch, hsel, htarget⟩ :=
    physical_successor_graph a.word next edge a.registers hpath hsuccessor
  have heq : i = a.index := path_index_unique i a.index a.word hword hindex
  subst i
  let b : Snapshot := ⟨next, gap', regs', reserve', head', finish, target⟩
  have hbgood : Good b := by
    change Grammar.LeafPath Grammar.nodes 157 next ∧ next.length + gap' = 3819 ∧
      paths[target]? = some next ∧ Canonical next gap' regs' reserve' head' [] finish
    exact ⟨hnext, by omega, htarget, hafter⟩
  have hagood : Good a := ⟨hleaf, hsum, hindex, hrel⟩
  exact ⟨b, duration, events, ⟨hagood, hbgood, edge, op, dest, extra, hpath, heffect,
    hsuccessor, hi, hrow, hlabel, hbranch, hpositive, hblock⟩, hbgood⟩

def initial : Snapshot := ⟨BlankFirst.word, 3815, BlankFirst.zeros, BlankFirst.reserve,
    -3818, (machineWordSystem raw rawLabels).run 89821408, 0⟩

theorem initial_good : Good initial := by
  refine ⟨Redispatch.named_leaf_path BlankFirst.path, by decide, ?_, raw_initial_canonical_budget.1⟩
  decide

inductive GraphWalk (start : Snapshot) : Nat → Nat → List Bool → Snapshot → Prop where
  | nil : GraphWalk start 0 0 [] start
  | snoc {n elapsed : Nat} {priorOut events : List Bool} {before after : Snapshot} {duration : Nat}
      (prior : GraphWalk start n elapsed priorOut before) (step : GraphStep before after duration events) :
      GraphWalk start (n+1) (elapsed+duration) (priorOut ++ events) after

/-- Every finite graph-walk length is realized on the one raw blank-start run. -/
theorem blank_graph_walk (n : Nat) :
    ∃ elapsed events finish, n ≤ elapsed ∧ GraphWalk initial n elapsed events finish ∧ Good finish ∧
      finish.config = (machineWordSystem raw rawLabels).run (89821408 + elapsed) ∧
      (machineWordSystem raw rawLabels).prefixWord (89821408 + elapsed) = events := by
  induction n with
  | zero =>
    refine ⟨0, [], initial, by omega, .nil, initial_good, ?_, ?_⟩
    · rw [Nat.add_zero]; rfl
    · rw [Nat.add_zero]; exact raw_initial_canonical_budget.2.2
  | succ n ih =>
    obtain ⟨elapsed, events, before, ht, hwalk, hgood, hrun, hprefix⟩ := ih
    obtain ⟨after, duration, out, hstep, hgood'⟩ := good_step before hgood
    obtain ⟨hbefore, hafter, edge, op, dest, extra, hpath, heffect, hsuccessor, hi, hrow, hlabel, hbranch, hpositive, hblock⟩ := hstep
    have hstep' : GraphStep before after duration out :=
      ⟨hbefore, hafter, edge, op, dest, extra, hpath, heffect, hsuccessor, hi, hrow, hlabel, hbranch, hpositive, hblock⟩
    refine ⟨elapsed + duration, events ++ out, after, by omega, .snoc hwalk hstep', hgood', ?_, ?_⟩
    · rw [← Nat.add_assoc, WordEventSystem.run_add, ← hrun]
      exact hblock.endpoint.symm
    · rw [← Nat.add_assoc, WordEventSystem.prefix_add, hprefix, ← hrun, hblock.output]

/-- The same continuous indexed graph walk and exact output prefix belong to
the selected literal 236-state blank-start execution. -/
theorem selected_blank_graph_walk (n : Nat) :
    ∃ elapsed events finish, n ≤ elapsed ∧ GraphWalk initial n elapsed events finish ∧ Good finish ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run (89821408 + elapsed) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + elapsed) = events := by
  obtain ⟨elapsed, events, finish, ht, hwalk, hgood, hrun, hprefix⟩ := blank_graph_walk n
  refine ⟨elapsed, events, finish, ht, hwalk, hgood, ?_, ?_⟩
  · rw [hrun, machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  · rw [← prefix_eq, hprefix]
end PASoundness.M236.OccurrenceGraph
