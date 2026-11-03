import Shared.PNP.Record285.GrammarGraphCheck

/-! Soundness of the finite grammar-to-literal-table certificate. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.Beeping.Machines
open Shared.PNP.Record285.GenericDispatch

attribute [local irreducible] fastNodes

 theorem chunk_sound (start count : Nat) (h : chunkCheck start count = true)
    (n : Nat) (hmem : n ∈ List.range' start count) : nodeCheck n = true :=
  List.all_eq_true.mp h n hmem

theorem chunk_interval (start count : Nat) (h : chunkCheck start count = true)
    (n : Nat) (hlo : start ≤ n) (hhi : n < start+count) : nodeCheck n = true := by
  apply chunk_sound start count h n ?_
  simp only [List.mem_range']
  refine ⟨n-start,?_,?_⟩ <;> omega

theorem checked_node (n : Nat) (hn : n < 163) : nodeCheck n = true := by
  by_cases h0 : n < 8
  · exact chunk_interval 0 8 chunk0 n (by omega) (by omega)
  by_cases h1 : n < 16
  · exact chunk_interval 8 8 chunk1 n (by omega) (by omega)
  by_cases h2 : n < 24
  · exact chunk_interval 16 8 chunk2 n (by omega) (by omega)
  by_cases h3 : n < 32
  · exact chunk_interval 24 8 chunk3 n (by omega) (by omega)
  by_cases h4 : n < 40
  · exact chunk_interval 32 8 chunk4 n (by omega) (by omega)
  by_cases h5 : n < 48
  · exact chunk_interval 40 8 chunk5 n (by omega) (by omega)
  by_cases h6 : n < 56
  · exact chunk_interval 48 8 chunk6 n (by omega) (by omega)
  by_cases h7 : n < 64
  · exact chunk_interval 56 8 chunk7 n (by omega) (by omega)
  by_cases h8 : n < 72
  · exact chunk_interval 64 8 chunk8 n (by omega) (by omega)
  by_cases h9 : n < 80
  · exact chunk_interval 72 8 chunk9 n (by omega) (by omega)
  by_cases h10 : n < 88
  · exact chunk_interval 80 8 chunk10 n (by omega) (by omega)
  by_cases h11 : n < 96
  · exact chunk_interval 88 8 chunk11 n (by omega) (by omega)
  by_cases h12 : n < 104
  · exact chunk_interval 96 8 chunk12 n (by omega) (by omega)
  by_cases h13 : n < 112
  · exact chunk_interval 104 8 chunk13 n (by omega) (by omega)
  by_cases h14 : n < 120
  · exact chunk_interval 112 8 chunk14 n (by omega) (by omega)
  by_cases h15 : n < 128
  · exact chunk_interval 120 8 chunk15 n (by omega) (by omega)
  by_cases h16 : n < 136
  · exact chunk_interval 128 8 chunk16 n (by omega) (by omega)
  by_cases h17 : n < 144
  · exact chunk_interval 136 8 chunk17 n (by omega) (by omega)
  by_cases h18 : n < 152
  · exact chunk_interval 144 8 chunk18 n (by omega) (by omega)
  by_cases h19 : n < 160
  · exact chunk_interval 152 8 chunk19 n (by omega) (by omega)
  exact chunk_interval 160 3 chunk20 n (by omega) (by omega)

def nodeEdge (n : Nat) (b : Bool) : Option Edge :=
  (nodes[n]?).map (fun p => if b then p.2 else p.1)

theorem mapped_lookup_bound {α β : Type} (xs : Array α) (f : α → β) (n : Nat) (v : β)
    (h : (xs[n]?).map f = some v) : n < xs.size := by
  by_cases hb : n < xs.size
  · exact hb
  have hn : xs[n]? = none := Array.getElem?_eq_none_iff.mpr (by omega)
  rw [hn] at h
  contradiction

def checkNodeAt (xs : Array Node) (q : Fin 285) (n : Nat) : Bool :=
  match xs[n]? with
  | none => false
  | some pair => checkEdge q false pair.1 && checkEdge q true pair.2

theorem checked_edge_of_lookup (xs : Array Node) (q : Fin 285) (n : Nat) (b : Bool) (e : Edge)
    (h : (xs[n]?).map (fun p => if b then p.2 else p.1) = some e)
    (hc : checkNodeAt xs q n = true) : checkEdge q b e = true := by
  cases hn : xs[n]? with
  | none => simp [hn] at h
  | some pair =>
    simp only [checkNodeAt,hn,Bool.and_eq_true] at hc
    cases b with
    | false =>
      simp only [hn,Option.map_some,Bool.false_eq_true,if_false,Option.some.injEq] at h
      subst e
      exact hc.1
    | true =>
      simp only [hn,Option.map_some,if_true,Option.some.injEq] at h
      subst e
      exact hc.2

theorem edge_check (n : Nat) (b : Bool) (e : Edge) (h : nodeEdge n b = some e) :
    checkEdge (state n) b e = true := by
  have hfast : (fastNodes[n]?).map (fun p => if b then p.2 else p.1) = some e := by
    simpa only [nodeEdge,nodes_fast] using h
  have hbound := mapped_lookup_bound fastNodes (fun p => if b then p.2 else p.1) n e hfast
  have hlt : n < 163 := by simpa only [nodes_size] using hbound
  have hc : checkNodeAt fastNodes (state n) n = true := checked_node n hlt
  exact checked_edge_of_lookup fastNodes (state n) n b e hfast hc

theorem edge_verified (n : Nat) (b : Bool) (e : Edge) (h : nodeEdge n b = some e) :
    ∃ row, expected e b = some row ∧ NumericTables.target.table.row (state n) b = row := by
  have hc := edge_check n b e h
  cases he : expected e b with
  | none => simp [checkEdge,he] at hc
  | some row =>
    refine ⟨row,rfl,?_⟩
    simpa only [checkEdge,he,decide_eq_true_eq] using hc

/-- Interpret a bit path in the finite DAG. A leaf is returned only when the
whole path is consumed; missing nodes and extra bits are rejected. -/
def walk (n : Nat) : List Bool → Option Edge
  | [] => none
  | b::bs =>
    match nodeEdge n b with
    | none => none
    | some (.node j) => walk j bs
    | some e => if bs.isEmpty then some e else none

/-- Any typed grammar path ending in an increment is exactly a preserving
literal dispatcher route to that physical field's increment terminal. -/
theorem walk_increment_route (code : List Bool) (n i : Nat)
    (hwalk : walk n code = some (.inc i)) :
    i < 15 ∧ route (state n) code = some (IncrementPreparation.terminal i) := by
  induction code generalizing n with
  | nil => simp [walk] at hwalk
  | cons b bs ih =>
    cases he : nodeEdge n b with
    | none => simp [walk,he] at hwalk
    | some e =>
      obtain ⟨row,hget,hrow⟩ := edge_verified n b e he
      cases e with
      | node j =>
        simp only [walk,he] at hwalk
        simp only [expected] at hget
        split at hget
        next hj =>
          simp only [Option.some.injEq] at hget
          rw [← hget] at hrow
          have ht := ih j hwalk
          refine ⟨ht.1,?_⟩
          simp only [route,hrow,if_true,true_and]
          exact ht.2
        next hj => contradiction
      | inc j =>
        cases bs with
        | nil =>
          simp only [walk,he,List.isEmpty_nil,if_true,Option.some.injEq,Edge.inc.injEq] at hwalk
          subst j
          simp only [expected] at hget
          split at hget
          next hj =>
            simp only [Option.some.injEq] at hget
            rw [← hget] at hrow
            exact ⟨hj, by simp [route,hrow]⟩
          next hj => contradiction
        | cons x xs => simp [walk,he] at hwalk
      | dec j => cases bs <;> simp [walk,he] at hwalk
      | half j => cases bs <;> simp [walk,he] at hwalk
      | beep => cases bs <;> simp [walk,he] at hwalk
      | brk j => cases bs <;> simp [walk,he] at hwalk
      | cont j => cases bs <;> simp [walk,he] at hwalk

theorem root_increment_route (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.inc i)) :
    i < 15 ∧ route treeRoot code = some (IncrementPreparation.terminal i) := by
  have h := walk_increment_route code 162 i hwalk
  simpa only [root_state] using h

end Shared.PNP.Record285.Grammar
