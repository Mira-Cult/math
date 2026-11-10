import PASoundness.M236OccurrenceGraphAdapters
/-! Connect physical successor paths to the retained finite graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236
open PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

theorem occurrence_index (word : List Bool) (h : Grammar.LeafPath Grammar.nodes 157 word) :
    ∃ i, i < 760 ∧ paths[i]? = some word := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem (Grammar.every_leaf_path word h)
  refine ⟨i, by simpa only [Grammar.leaf_count] using hi, ?_⟩
  change Grammar.completePaths.toArray[i]? = some word
  rw [List.getElem?_toArray, List.getElem?_eq_getElem hi, he]

theorem witness_row_exists (i : Nat) (hi : i < 760) :
    ∃ op dest extra, sourceRows[i]? = some (op, dest, extra) := by
  have hsize : i < sourceRows.size := by rw [graph_size]; exact hi
  cases hrow : sourceRows[i]? with
  | none =>
    have hsome : (sourceRows[i]?).isSome = true := by simp [hsize]
    rw [hrow] at hsome
    contradiction
  | some row =>
    rcases row with ⟨op, dest, extra⟩
    exact ⟨op, dest, extra, rfl⟩

/-- The graph records administrative transfers as jumps and keeps the
literal operation name for register and output leaves. -/
def GraphLabel (edge : Grammar.Edge) (op : String) : Prop :=
  match edge with
  | .node _ => False
  | .leaf name .. =>
    if name = "_continue.1" ∨ name = "_continue.2" ∨ name = "_continue.3" ∨
       name = "_break.1" ∨ name = "_break.3" then op = "jump" else op = name

theorem ordinary_graph_label (name op : String) (target : Fin 237)
    (write : Bool) (move : Move) (event : Option Bool)
    (hordinary : OrdinaryName name) (hop : op = name) :
    GraphLabel (.leaf name target write move event) op := by
  rcases hord : hordinary with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  simp [GraphLabel, h1, h2, h3, h4, h5, hop]

/-- Which edge a physical branch takes, including the register zero test. -/
inductive GraphBranch : Grammar.Edge → RegisterMachine.Bank 9 → Nat → Option Nat → Nat → Prop where
  | inc (r : Fin 9) (write : Bool) (bank : RegisterMachine.Bank 9) (dest : Nat) (extra : Option Nat) :
      GraphBranch (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none) bank dest extra dest
  | positive (r : Fin 9) (write : Bool) (bank : RegisterMachine.Bank 9) (dest : Nat) (extra : Option Nat)
      (v : Nat) (h : bank r = v + 1) :
      GraphBranch (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none) bank dest extra dest
  | zero (r : Fin 9) (write : Bool) (bank : RegisterMachine.Bank 9) (dest target : Nat) (h : bank r = 0) :
      GraphBranch (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none) bank dest (some target) target
  | continue1 (bank : RegisterMachine.Bank 9) (dest : Nat) (extra : Option Nat) :
      GraphBranch (.leaf "_continue.1" 72 false .left none) bank dest extra dest
  | continue2 (bank : RegisterMachine.Bank 9) (dest : Nat) (extra : Option Nat) :
      GraphBranch (.leaf "_continue.2" 73 false .left none) bank dest extra dest
  | continue3 (bank : RegisterMachine.Bank 9) (dest : Nat) (extra : Option Nat) :
      GraphBranch (.leaf "_continue.3" 74 false .left none) bank dest extra dest
  | break1 (bank : RegisterMachine.Bank 9) (dest : Nat) (extra : Option Nat) :
      GraphBranch (.leaf "_break.1" 69 false .left none) bank dest extra dest
  | break3 (bank : RegisterMachine.Bank 9) (dest : Nat) (extra : Option Nat) :
      GraphBranch (.leaf "_break.3" 71 false .left none) bank dest extra dest
  | emitContinue (b : Bool) (bank : RegisterMachine.Bank 9) (dest : Nat) (extra : Option Nat) :
      GraphBranch (.leaf (Emit.emitName b) 72 true .left (some b)) bank dest extra dest
  | emitCleanup (b : Bool) (bank : RegisterMachine.Bank 9) (dest : Nat) (extra : Option Nat) :
      GraphBranch (.leaf (Emit.emitName b) 68 false .left (some b)) bank dest extra dest

/-- Every literal physical control successor selects an edge of the retained
finite graph, with the matching next path. No source-program semantics is assumed. -/
theorem physical_successor_graph (word next : List Bool) (edge : Grammar.Edge)
    (bank : RegisterMachine.Bank 9)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word edge)
    (hstep : ControlSuccessor edge bank word next) :
    ∃ i op dest extra target, i < 760 ∧
      sourceRows[i]? = some (op, dest, extra) ∧ paths[i]? = some word ∧
      GraphLabel edge op ∧ GraphBranch edge bank dest extra target ∧
      (target = dest ∨ extra = some target) ∧ paths[target]? = some next := by
  obtain ⟨i, hi, hword⟩ := occurrence_index word (Redispatch.named_leaf_path hpath)
  obtain ⟨op, dest, extra, hrow⟩ := witness_row_exists i hi
  cases hstep with
  | inc r write bank word next h =>
    have hn := Continue.pathName_named hpath
    simp only [Continue.edgeName] at hn
    obtain ⟨hop, ht⟩ := ordinary_edge_matches i hi word next _ op dest extra hrow hword hn
      (register_names_ordinary r).1 h
    exact ⟨i, op, dest, extra, dest, hi, hrow, hword,
      ordinary_graph_label _ _ _ _ _ _ (register_names_ordinary r).1 hop,
      .inc r write bank dest extra, Or.inl rfl, ht⟩
  | positive r write bank word next v hv h =>
    have hn := Continue.pathName_named hpath
    simp only [Continue.edgeName] at hn
    obtain ⟨hop, ht⟩ := ordinary_edge_matches i hi word next _ op dest extra hrow hword hn
      (register_names_ordinary r).2 h
    exact ⟨i, op, dest, extra, dest, hi, hrow, hword,
      ordinary_graph_label _ _ _ _ _ _ (register_names_ordinary r).2 hop,
      .positive r write bank dest extra v hv, Or.inl rfl, ht⟩
  | zero r write bank word next hz bit tail hd hn =>
    obtain ⟨z, he, ht⟩ := zero_edge_matches i hi r write word next tail bit op dest extra hrow hword hpath hd hn
    have hname := Continue.pathName_named hpath
    simp only [Continue.edgeName] at hname
    obtain ⟨hop, _⟩ := ordinary_row_matches i hi word _ op dest extra hrow hword hname
      (register_names_ordinary r).2
    refine ⟨i, op, dest, extra, z, hi, hrow, hword,
      ordinary_graph_label _ _ _ _ _ _ (register_names_ordinary r).2 hop, ?_, Or.inr he, ht⟩
    rw [he]
    exact .zero r write bank dest z hz
  | continue1 bank word next source hs hn =>
    obtain ⟨hop, he, ht⟩ := continue1_edge_matches i hi word next source op dest extra hrow hword hpath hs hn
    exact ⟨i, op, dest, extra, dest, hi, hrow, hword, by simpa [GraphLabel] using hop, .continue1 bank dest extra, Or.inl rfl, ht⟩
  | continue2 bank word next source hs hn =>
    obtain ⟨hop, he, ht⟩ := continue2_edge_matches i hi word next source op dest extra hrow hword hpath hs hn
    exact ⟨i, op, dest, extra, dest, hi, hrow, hword, by simpa [GraphLabel] using hop, .continue2 bank dest extra, Or.inl rfl, ht⟩
  | continue3 bank word next source hs hn =>
    obtain ⟨hop, he, ht⟩ := continue3_edge_matches i hi word next source op dest extra hrow hword hpath hs hn
    exact ⟨i, op, dest, extra, dest, hi, hrow, hword, by simpa [GraphLabel] using hop, .continue3 bank dest extra, Or.inl rfl, ht⟩
  | break1 bank word next source hs hn =>
    obtain ⟨hop, he, ht⟩ := break1_edge_matches i hi word next source op dest extra hrow hword hpath hs hn
    exact ⟨i, op, dest, extra, dest, hi, hrow, hword, by simpa [GraphLabel] using hop, .break1 bank dest extra, Or.inl rfl, ht⟩
  | break3 bank word next source hs hn =>
    obtain ⟨hop, he, ht⟩ := break3_edge_matches i hi word next source op dest extra hrow hword hpath hs hn
    exact ⟨i, op, dest, extra, dest, hi, hrow, hword, by simpa [GraphLabel] using hop, .break3 bank dest extra, Or.inl rfl, ht⟩
  | emitContinue bit bank word next source hs hn =>
    cases bit with
    | false =>
      have hp : Preparation.NamedPath Grammar.nodes 157 word (.leaf "emit.0" 72 true .left (some false)) := by
        simpa [Emit.emitName] using hpath
      obtain ⟨hop, he, ht⟩ := emit0_continue_edge_matches i hi word next source op dest extra hrow hword hp hs hn
      exact ⟨i, op, dest, extra, dest, hi, hrow, hword, by simpa [GraphLabel, Emit.emitName] using hop, .emitContinue _ bank dest extra, Or.inl rfl, ht⟩
    | true =>
      have hp : Preparation.NamedPath Grammar.nodes 157 word (.leaf "emit.1" 72 true .left (some true)) := by
        simpa [Emit.emitName] using hpath
      obtain ⟨hop, he, ht⟩ := emit1_continue_edge_matches i hi word next source op dest extra hrow hword hp hs hn
      exact ⟨i, op, dest, extra, dest, hi, hrow, hword, by simpa [GraphLabel, Emit.emitName] using hop, .emitContinue _ bank dest extra, Or.inl rfl, ht⟩
  | emitCleanup bit bank word next source hs hn =>
    cases bit with
    | false =>
      have hp : Preparation.NamedPath Grammar.nodes 157 word (.leaf "emit.0" 68 false .left (some false)) := by
        simpa [Emit.emitName] using hpath
      obtain ⟨hop, he, ht⟩ := emit0_cleanup_edge_matches i hi word next source op dest extra hrow hword hp hs hn
      exact ⟨i, op, dest, extra, dest, hi, hrow, hword, by simpa [GraphLabel, Emit.emitName] using hop, .emitCleanup _ bank dest extra, Or.inl rfl, ht⟩
    | true =>
      have hp : Preparation.NamedPath Grammar.nodes 157 word (.leaf "emit.1" 68 false .left (some true)) := by
        simpa [Emit.emitName] using hpath
      obtain ⟨hop, he, ht⟩ := emit1_cleanup_edge_matches i hi word next source op dest extra hrow hword hp hs hn
      exact ⟨i, op, dest, extra, dest, hi, hrow, hword, by simpa [GraphLabel, Emit.emitName] using hop, .emitCleanup _ bank dest extra, Or.inl rfl, ht⟩
end PASoundness.M236.OccurrenceGraph
