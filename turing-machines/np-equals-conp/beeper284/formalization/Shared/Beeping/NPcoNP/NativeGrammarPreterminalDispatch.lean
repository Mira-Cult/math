import Shared.Beeping.NPcoNP.NativeRightDispatchGeneric
import Shared.Beeping.NPcoNP.Grammar284ExpansionPaths

/-! The literal table silently follows every expanded producer leaf path up
to, but not including, its final control bit. Operation semantics are separate. -/
namespace Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeRightDispatchGeneric
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 100000000

def leafDispatchOK (entry : Path × String) : Bool :=
  (followRight 93 entry.1.tail.dropLast).isSome

/-- Kernel-check the finite literal-table dispatch paths for every expanded
producer leaf, stopping before the final bit. -/
theorem all_leaf_paths_checked : traceState557.acc.leaves.toList.all leafDispatchOK = true := by
  decide

/-- Any listed leaf's preterminal path has a checked final table state. -/
theorem leaf_preterminal_checked (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList) :
    ∃ q, followRight 93 entry.1.tail.dropLast=some q := by
  have h := List.all_eq_true.mp all_leaf_paths_checked entry member
  cases he : followRight 93 entry.1.tail.dropLast with
  | none => simp [leafDispatchOK,he] at h
  | some q => exact ⟨q,rfl⟩

/-- On any tape containing a listed preterminal path, the literal machine
reaches its checked preterminal state silently, in exactly the word length,
with the entire tape unchanged. -/
theorem leaf_preterminal_dispatch (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList) (h : Int) (t : Int → Bool)
    (layout : Holds t h entry.1.tail.dropLast) :
    ∃ q, silentSegment machine (cfg 93 h t)
      (cfg q (h+(entry.1.tail.dropLast.length : Int)) t) entry.1.tail.dropLast.length := by
  obtain ⟨q,hq⟩ := leaf_preterminal_checked entry member
  exact ⟨q,dispatch 93 q h t entry.1.tail.dropLast hq layout⟩

/-- These four producer leaves implement administrative control movement. -/
def administrative (name : String) : Bool :=
  name == "_continue.1" || name == "_continue.2" ||
    name == "_break.1" || name == "_break.2"

def leafFullClassificationOK (entry : Path × String) : Bool :=
  (followRight 93 entry.1.tail).isSome == !(administrative entry.2)

/-- Exactly the administrative leaves fail the silent, unchanged-right test
on their final control transition; every other listed leaf satisfies it through
the full path. This is a literal finite-table check, not operation correctness. -/
theorem all_leaf_full_paths_classified :
    traceState557.acc.leaves.toList.all leafFullClassificationOK = true := by
  decide

theorem producer_leaf_counts : traceState557.acc.leaves.size=279 ∧
    (traceState557.acc.leaves.toList.filter (fun e => !(administrative e.2))).length=185 := by
  decide

/-- A non-administrative producer leaf has a checked complete dispatch state. -/
theorem ordinary_leaf_checked (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList)
    (ordinary : administrative entry.2=false) :
    ∃ q, followRight 93 entry.1.tail=some q := by
  have hc := List.all_eq_true.mp all_leaf_full_paths_classified entry member
  simp only [leafFullClassificationOK,beq_iff_eq,ordinary,Bool.not_false] at hc
  cases he : followRight 93 entry.1.tail with
  | none => simp [he] at hc
  | some q => exact ⟨q,rfl⟩

/-- For any listed ordinary operation leaf, its entire supplied control word
is traversed silently and without changing the tape, ending at its checked
literal-table operation entry. The operation itself is not executed here. -/
theorem ordinary_leaf_dispatch (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList)
    (ordinary : administrative entry.2=false) (h : Int) (t : Int → Bool)
    (layout : Holds t h entry.1.tail) :
    ∃ q, silentSegment machine (cfg 93 h t)
      (cfg q (h+(entry.1.tail.length : Int)) t) entry.1.tail.length := by
  obtain ⟨q,hq⟩ := ordinary_leaf_checked entry member ordinary
  exact ⟨q,dispatch 93 q h t entry.1.tail hq layout⟩

/-- The ordinary-leaf theorem applies directly to the certified producer
grammar expansion, not merely to an arbitrary supplied list. -/
theorem expanded_ordinary_leaf_dispatch (e : Expansion)
    (expanded : expand producerGrammar.nodes 53 (.node producerGrammar.root)
      [true,true,false] [] {} = some e)
    (entry : Path × String) (member : entry ∈ e.leaves.toList)
    (ordinary : administrative entry.2=false) (h : Int) (t : Int → Bool)
    (layout : Holds t h entry.1.tail) :
    ∃ q, silentSegment machine (cfg 93 h t)
      (cfg q (h+(entry.1.tail.length : Int)) t) entry.1.tail.length := by
  rw [producerExpand] at expanded
  cases expanded
  exact ordinary_leaf_dispatch entry member ordinary h t layout

/-- Expected literal entry state for each ordinary producer operation. The
administrative names have no unchanged-right complete dispatch entry. -/
def operationEntry : String → Option (Fin 284)
  | "beep" => some 99
  | "3.$coalesced.4.decnz" => some 62
  | "3.$coalesced.10.inc" => some 55
  | "3.$coalesced.9.inc" => some 73
  | "3.$coalesced.9.decnz" => some 72
  | "3.$coalesced.4.inc" => some 63
  | "3.$coalesced.0.decnz" => some 50
  | "3.$coalesced.10.decnz" => some 54
  | "3.$coalesced.0.inc" => some 51
  | "3.$coalesced.5.decnz" => some 64
  | "3.$coalesced.6.decnz" => some 66
  | "3.$coalesced.6.inc" => some 67
  | "3.$native-half:$coalesced.0.decnz" => some 74
  | "3.$coalesced.5.inc" => some 65
  | "3.$coalesced.7.decnz" => some 68
  | "3.$coalesced.7.inc" => some 69
  | "3.$coalesced.8.decnz" => some 70
  | "3.$coalesced.8.inc" => some 71
  | "3.$coalesced.1.decnz" => some 52
  | "3.$coalesced.2.decnz" => some 58
  | "3.$coalesced.2.inc" => some 59
  | "3.$coalesced.11.inc" => some 57
  | "3.$coalesced.11.decnz" => some 56
  | "3.$native-half:$coalesced.1.decnz" => some 75
  | "3.$native-half:$coalesced.9.decnz" => some 77
  | "3.$native-half:$coalesced.2.decnz" => some 76
  | "3.$coalesced.1.inc" => some 53
  | "3.$coalesced.3.decnz" => some 60
  | "3.$coalesced.3.inc" => some 61
  | _ => none

def leafEntryOK (entry : Path × String) : Bool :=
  followRight 93 entry.1.tail == operationEntry entry.2

/-- Every expanded leaf's literal path agrees with its operation entry map.
This verifies the finite dispatch table, not the subsequent operation effect. -/
theorem all_leaf_entry_states_checked :
    traceState557.acc.leaves.toList.all leafEntryOK = true := by
  decide

theorem leaf_entry_checked (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList) :
    followRight 93 entry.1.tail=operationEntry entry.2 := by
  have h := List.all_eq_true.mp all_leaf_entry_states_checked entry member
  simpa only [leafEntryOK,beq_iff_eq] using h

/-- A listed operation whose entry map is `some q` reaches that precise
literal state silently on every supplied tape matching its control path. -/
theorem leaf_dispatch_to_entry (entry : Path × String)
    (member : entry ∈ traceState557.acc.leaves.toList) (q : Fin 284)
    (entry_state : operationEntry entry.2=some q) (h : Int) (t : Int → Bool)
    (layout : Holds t h entry.1.tail) :
    silentSegment machine (cfg 93 h t)
      (cfg q (h+(entry.1.tail.length : Int)) t) entry.1.tail.length := by
  have checked := (leaf_entry_checked entry member).trans entry_state
  exact dispatch 93 q h t entry.1.tail checked layout

/-- The entry-state theorem applies directly to the certified producer
expansion. The supplied tape still must satisfy the stated layout. -/
theorem expanded_leaf_dispatch_to_entry (e : Expansion)
    (expanded : expand producerGrammar.nodes 53 (.node producerGrammar.root)
      [true,true,false] [] {} = some e)
    (entry : Path × String) (member : entry ∈ e.leaves.toList) (q : Fin 284)
    (entry_state : operationEntry entry.2=some q) (h : Int) (t : Int → Bool)
    (layout : Holds t h entry.1.tail) :
    silentSegment machine (cfg 93 h t)
      (cfg q (h+(entry.1.tail.length : Int)) t) entry.1.tail.length := by
  rw [producerExpand] at expanded
  cases expanded
  exact leaf_dispatch_to_entry entry member q entry_state h t layout

#print axioms all_leaf_entry_states_checked
#print axioms expanded_leaf_dispatch_to_entry

#print axioms expanded_ordinary_leaf_dispatch

#print axioms all_leaf_full_paths_classified
#print axioms ordinary_leaf_dispatch

#print axioms all_leaf_paths_checked
#print axioms leaf_preterminal_dispatch
end Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
