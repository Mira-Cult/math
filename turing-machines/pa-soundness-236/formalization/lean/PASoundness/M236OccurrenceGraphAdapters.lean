import PASoundness.M236OccurrenceGraphSound
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
/-! Physical control successor adapters for the finite graph witness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236
open PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines


theorem cyclic_next_get {α : Type} (xs : List α) (d : α) (n : Nat) (h : n < xs.length) :
    (xs.drop 1 ++ [xs.headD d])[n]? = xs[(n+1) % xs.length]? := by
  by_cases hn : n + 1 < xs.length
  · have hl : n < (xs.drop 1).length := by simp only [List.length_drop]; omega
    rw [List.getElem?_append_left hl, List.getElem?_drop]
    have hm : (n+1) % xs.length = n+1 := Nat.mod_eq_of_lt hn
    simpa [hm, Nat.add_comm]
  · have he : n+1 = xs.length := by omega
    have hl : (xs.drop 1).length ≤ n := by simp only [List.length_drop]; omega
    rw [List.getElem?_append_right hl]
    have hz : n - (xs.drop 1).length = 0 := by simp only [List.length_drop]; omega
    rw [hz, he, Nat.mod_self]
    cases xs with
    | nil => simp at h
    | cons x rest => simp

theorem adjacent_index (i : Nat) (hi : i < 760) (word next : List Bool)
    (hword : paths[i]? = some word) (hnext : paths[(i+1)%760]? = some next) :
    (word, next) ∈ adjacentPaths := by
  have hlen : Grammar.completePaths.length = 760 := Grammar.leaf_count
  have hw : Grammar.completePaths[i]? = some word := by simpa only [paths, List.getElem?_toArray] using hword
  have hn : Grammar.completePaths[(i+1)%Grammar.completePaths.length]? = some next := by
    rw [hlen]
    simpa only [paths, List.getElem?_toArray] using hnext
  have hi' : i < Grammar.completePaths.length := by omega
  have hsecond : (Grammar.completePaths.drop 1 ++ [Grammar.completePaths.headD []])[i]? = some next := by
    rw [cyclic_next_get _ _ _ hi']
    exact hn
  have hpair : adjacentPaths[i]? = some (word, next) := by
    apply List.getElem?_zip_eq_some.mpr
    exact ⟨hw, hsecond⟩
  obtain ⟨hbound, heq⟩ := List.getElem?_eq_some_iff.mp hpair
  rw [← heq]
  exact List.getElem_mem hbound


def OrdinaryName (name : String) : Prop :=
  name ≠ "_continue.1" ∧ name ≠ "_continue.2" ∧ name ≠ "_continue.3" ∧
  name ≠ "_break.1" ∧ name ≠ "_break.3" ∧ name ≠ "emit.0" ∧ name ≠ "emit.1"

instance (name : String) : Decidable (OrdinaryName name) := by unfold OrdinaryName; infer_instance

theorem register_names_ordinary : ∀ r : Fin 9,
    OrdinaryName ("3." ++ Selector.registerNames[r] ++ ".inc") ∧
    OrdinaryName ("3." ++ Selector.registerNames[r] ++ ".decnz") := by decide

theorem ordinary_row_matches (i : Nat) (hi : i < 760) (word : List Bool)
    (name op : String) (dest : Nat) (extra : Option Nat)
    (hrow : sourceRows[i]? = some (op, dest, extra)) (hword : paths[i]? = some word)
    (hname : Continue.pathName 157 word = some name) (hordinary : OrdinaryName name) :
    op = name ∧ dest = (i+1)%760 := by
  have hc := every_occurrence_correct i hi
  unfold RowCorrect at hc
  rw [hrow, hword] at hc
  dsimp only at hc
  rw [hname] at hc
  rcases hord : hordinary with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  simp only [h1, h2, h3, h4, h5, h6, h7] at hc
  exact ⟨hc.2.1, hc.2.2.1⟩


/-- A zero-decrement physical successor is the witness graph's zero edge. -/
theorem zero_edge_matches (i : Nat) (hi : i < 760)
    (r : Fin 9) (write : Bool) (word next tail : List Bool) (bit : Bool)
    (op : String) (dest : Nat) (extra : Option Nat)
    (hrow : sourceRows[i]? = some (op, dest, extra))
    (hword : paths[i]? = some word)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (hdecode : decodeZero word = some (bit, tail))
    (hresolve : resolveZeros Grammar.nodes 158 157 tail = some next) :
    ∃ z, extra = some z ∧ paths[z]? = some next := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  have hc := every_occurrence_correct i hi
  unfold RowCorrect at hc
  rw [hrow, hword] at hc
  dsimp only at hc
  rw [hn] at hc
  fin_cases r <;>
    simp [Selector.registerNames, isDec, hdecode, hresolve] at hc ⊢ <;>
    aesop


theorem continue1_edge_matches (i : Nat) (hi : i < 760)
    (word next source : List Bool) (op : String) (dest : Nat) (extra : Option Nat)
    (hrow : sourceRows[i]? = some (op, dest, extra)) (hword : paths[i]? = some word)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word (.leaf "_continue.1" 72 false .left none))
    (hsource : Continue.restartPrefix 1 word = some source)
    (hresolve : resolveZeros Grammar.nodes 158 157 source = some next) :
    op = "jump" ∧ extra = none ∧ paths[dest]? = some next := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  have hc := every_occurrence_correct i hi
  unfold RowCorrect at hc
  rw [hrow, hword] at hc
  try dsimp only at hc
  simp only [hn] at hc
  simp only [resolveWith, hsource, Option.bind_some, hresolve] at hc
  exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.symm⟩

theorem continue2_edge_matches (i : Nat) (hi : i < 760)
    (word next source : List Bool) (op : String) (dest : Nat) (extra : Option Nat)
    (hrow : sourceRows[i]? = some (op, dest, extra)) (hword : paths[i]? = some word)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word (.leaf "_continue.2" 73 false .left none))
    (hsource : Continue.restartPrefix 2 word = some source)
    (hresolve : resolveZeros Grammar.nodes 158 157 source = some next) :
    op = "jump" ∧ extra = none ∧ paths[dest]? = some next := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  have hc := every_occurrence_correct i hi
  unfold RowCorrect at hc
  rw [hrow, hword] at hc
  try dsimp only at hc
  simp only [hn] at hc
  simp only [resolveWith, hsource, Option.bind_some, hresolve] at hc
  exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.symm⟩

theorem continue3_edge_matches (i : Nat) (hi : i < 760)
    (word next source : List Bool) (op : String) (dest : Nat) (extra : Option Nat)
    (hrow : sourceRows[i]? = some (op, dest, extra)) (hword : paths[i]? = some word)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word (.leaf "_continue.3" 74 false .left none))
    (hsource : Continue.restartPrefix 3 word = some source)
    (hresolve : resolveZeros Grammar.nodes 158 157 source = some next) :
    op = "jump" ∧ extra = none ∧ paths[dest]? = some next := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  have hc := every_occurrence_correct i hi
  unfold RowCorrect at hc
  rw [hrow, hword] at hc
  try dsimp only at hc
  simp only [hn] at hc
  simp only [resolveWith, hsource, Option.bind_some, hresolve] at hc
  exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.symm⟩

theorem break1_edge_matches (i : Nat) (hi : i < 760)
    (word next source : List Bool) (op : String) (dest : Nat) (extra : Option Nat)
    (hrow : sourceRows[i]? = some (op, dest, extra)) (hword : paths[i]? = some word)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word (.leaf "_break.1" 69 false .left none))
    (hsource : Break.successorPrefix 1 word = some source)
    (hresolve : resolveZeros Grammar.nodes 158 157 source = some next) :
    op = "jump" ∧ extra = none ∧ paths[dest]? = some next := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  have hc := every_occurrence_correct i hi
  unfold RowCorrect at hc
  rw [hrow, hword] at hc
  try dsimp only at hc
  simp only [hn] at hc
  simp only [resolveWith, hsource, Option.bind_some, hresolve] at hc
  exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.symm⟩

theorem break3_edge_matches (i : Nat) (hi : i < 760)
    (word next source : List Bool) (op : String) (dest : Nat) (extra : Option Nat)
    (hrow : sourceRows[i]? = some (op, dest, extra)) (hword : paths[i]? = some word)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word (.leaf "_break.3" 71 false .left none))
    (hsource : Break.successorPrefix 3 word = some source)
    (hresolve : resolveZeros Grammar.nodes 158 157 source = some next) :
    op = "jump" ∧ extra = none ∧ paths[dest]? = some next := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  have hc := every_occurrence_correct i hi
  unfold RowCorrect at hc
  rw [hrow, hword] at hc
  try dsimp only at hc
  simp only [hn] at hc
  simp only [resolveWith, hsource, Option.bind_some, hresolve] at hc
  exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.symm⟩

theorem emit0_continue_edge_matches (i : Nat) (hi : i < 760)
    (word next source : List Bool) (op : String) (dest : Nat) (extra : Option Nat)
    (hrow : sourceRows[i]? = some (op, dest, extra)) (hword : paths[i]? = some word)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word (.leaf "emit.0" 72 true .left (some false)))
    (hsource : Break.successorPrefix 0 word = some source)
    (hresolve : resolveZeros Grammar.nodes 158 157 source = some next) :
    op = "emit.0" ∧ extra = none ∧ paths[dest]? = some next := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  have hc := every_occurrence_correct i hi
  unfold RowCorrect at hc
  rw [hrow, hword] at hc
  try dsimp only at hc
  simp only [hn] at hc
  simp only [resolveWith, hsource, Option.bind_some, hresolve] at hc
  exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.symm⟩

theorem emit0_cleanup_edge_matches (i : Nat) (hi : i < 760)
    (word next source : List Bool) (op : String) (dest : Nat) (extra : Option Nat)
    (hrow : sourceRows[i]? = some (op, dest, extra)) (hword : paths[i]? = some word)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word (.leaf "emit.0" 68 false .left (some false)))
    (hsource : Break.successorPrefix 0 word = some source)
    (hresolve : resolveZeros Grammar.nodes 158 157 source = some next) :
    op = "emit.0" ∧ extra = none ∧ paths[dest]? = some next := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  have hc := every_occurrence_correct i hi
  unfold RowCorrect at hc
  rw [hrow, hword] at hc
  try dsimp only at hc
  simp only [hn] at hc
  simp only [resolveWith, hsource, Option.bind_some, hresolve] at hc
  exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.symm⟩

theorem emit1_continue_edge_matches (i : Nat) (hi : i < 760)
    (word next source : List Bool) (op : String) (dest : Nat) (extra : Option Nat)
    (hrow : sourceRows[i]? = some (op, dest, extra)) (hword : paths[i]? = some word)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word (.leaf "emit.1" 72 true .left (some true)))
    (hsource : Break.successorPrefix 0 word = some source)
    (hresolve : resolveZeros Grammar.nodes 158 157 source = some next) :
    op = "emit.1" ∧ extra = none ∧ paths[dest]? = some next := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  have hc := every_occurrence_correct i hi
  unfold RowCorrect at hc
  rw [hrow, hword] at hc
  try dsimp only at hc
  simp only [hn] at hc
  simp only [resolveWith, hsource, Option.bind_some, hresolve] at hc
  exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.symm⟩

theorem emit1_cleanup_edge_matches (i : Nat) (hi : i < 760)
    (word next source : List Bool) (op : String) (dest : Nat) (extra : Option Nat)
    (hrow : sourceRows[i]? = some (op, dest, extra)) (hword : paths[i]? = some word)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word (.leaf "emit.1" 68 false .left (some true)))
    (hsource : Break.successorPrefix 0 word = some source)
    (hresolve : resolveZeros Grammar.nodes 158 157 source = some next) :
    op = "emit.1" ∧ extra = none ∧ paths[dest]? = some next := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  have hc := every_occurrence_correct i hi
  unfold RowCorrect at hc
  rw [hrow, hword] at hc
  try dsimp only at hc
  simp only [hn] at hc
  simp only [resolveWith, hsource, Option.bind_some, hresolve] at hc
  exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.symm⟩


/-- A physical adjacent return reaches the occurrence graph's ordinary edge. -/
theorem ordinary_edge_matches (i : Nat) (hi : i < 760) (word next : List Bool)
    (name op : String) (dest : Nat) (extra : Option Nat)
    (hrow : sourceRows[i]? = some (op, dest, extra)) (hword : paths[i]? = some word)
    (hname : Continue.pathName 157 word = some name) (hordinary : OrdinaryName name)
    (hpair : (word, next) ∈ adjacentPaths) :
    op = name ∧ paths[dest]? = some next := by
  obtain ⟨hop, hdest⟩ := ordinary_row_matches i hi word name op dest extra hrow hword hname hordinary
  have hc := every_occurrence_correct i hi
  unfold RowCorrect at hc
  rw [hrow, hword] at hc
  dsimp only at hc
  have hv : (paths[dest]?).isSome = true := hc.1
  cases ht : paths[dest]? with
  | none => simp [ht] at hv
  | some target =>
    have htarget : paths[(i+1)%760]? = some target := by rw [← hdest]; exact ht
    have hpair' := adjacent_index i hi word target hword htarget
    have he := adjacent_functional word next target hpair hpair'
    subst target
    exact ⟨hop, rfl⟩
end PASoundness.M236.OccurrenceGraph
