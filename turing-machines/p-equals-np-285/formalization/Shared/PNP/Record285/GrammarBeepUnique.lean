import Shared.PNP.Record285.GrammarBeepPhysical

/-! The unique complete beep path in the frozen producer grammar. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar

def noBeepAt (n : Nat) : Bool :=
  match fastNodes[n]? with
  | none => false
  | some p => (p.1 != .beep) && (p.2 != .beep)

theorem no_beep_below_160 : (List.range 160).all noBeepAt = true := by decide

attribute [local irreducible] fastNodes

theorem no_beep_edge (n : Nat) (hn : n < 160) (b : Bool) :
    nodeEdge n b ≠ some .beep := by
  have hc := List.all_eq_true.mp no_beep_below_160 n (List.mem_range.mpr hn)
  have hfast : nodeEdge n b = (fastNodes[n]?).map (fun p => if b then p.2 else p.1) := by
    simp only [nodeEdge,nodes_fast]
  rw [hfast]
  cases hp : fastNodes[n]? with
  | none => simp
  | some p =>
    simp only [noBeepAt,hp,Bool.and_eq_true, bne_iff_ne] at hc
    cases b <;> simp_all

theorem no_beep_walk (code : List Bool) (n : Nat) (hn : n < 160) :
    walk n code ≠ some .beep := by
  induction code generalizing n with
  | nil => simp [walk]
  | cons b bs ih =>
    cases he : nodeEdge n b with
    | none => simp [walk,he]
    | some e =>
      cases e with
      | node j =>
        have hj := node_edge_decreases n b j (by omega) he
        simpa only [walk,he] using ih j (by omega)
      | beep => exact False.elim ((no_beep_edge n hn b) he)
      | inc j => cases bs <;> simp [walk,he]
      | dec j => cases bs <;> simp [walk,he]
      | half j => cases bs <;> simp [walk,he]
      | brk j => cases bs <;> simp [walk,he]
      | cont j => cases bs <;> simp [walk,he]

theorem root_false_edge : nodeEdge 162 false = some (.inc 6) := by
  simp only [nodeEdge,nodes_fast,fastNodes]; decide
theorem root_true_edge : nodeEdge 162 true = some (.node 161) := by
  simp only [nodeEdge,nodes_fast,fastNodes]; decide
theorem next_false_edge : nodeEdge 161 false = some (.node 160) := by
  simp only [nodeEdge,nodes_fast,fastNodes]; decide
theorem next_true_edge : nodeEdge 161 true = some (.cont 1) := by
  simp only [nodeEdge,nodes_fast,fastNodes]; decide
theorem beep_false_edge : nodeEdge 160 false = some .beep := by
  simp only [nodeEdge,nodes_fast,fastNodes]; decide
theorem beep_true_edge : nodeEdge 160 true = some (.node 159) := by
  simp only [nodeEdge,nodes_fast,fastNodes]; decide

/-- There is exactly one complete root-to-beep grammar word. -/
theorem root_beep_word (code : List Bool) (hwalk : walk rootIndex code = some .beep) :
    code = [true,false,false] := by
  cases code with
  | nil => simp [walk] at hwalk
  | cons a as =>
    cases a with
    | false => cases as <;> simp [rootIndex,walk,root_false_edge] at hwalk
    | true =>
      cases as with
      | nil => simp [rootIndex,walk,root_true_edge] at hwalk
      | cons b bs =>
        cases b with
        | true => cases bs <;> simp [rootIndex,walk,root_true_edge,next_true_edge] at hwalk
        | false =>
          cases bs with
          | nil => simp [rootIndex,walk,root_true_edge,next_false_edge] at hwalk
          | cons c cs =>
            cases c with
            | false =>
              cases cs <;> simp [rootIndex,walk,root_true_edge,next_false_edge,beep_false_edge] at hwalk ⊢
            | true =>
              have hbad : walk 159 cs = some .beep := by
                simpa only [rootIndex,walk,root_true_edge,next_false_edge,beep_true_edge] using hwalk
              exact False.elim ((no_beep_walk cs 159 (by decide)) hbad)

end Shared.PNP.Record285.Grammar
