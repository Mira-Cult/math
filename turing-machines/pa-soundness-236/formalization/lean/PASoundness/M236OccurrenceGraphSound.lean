import PASoundness.M236OccurrenceGraphCheck
/-! Soundness of the reflected occurrence-graph comparison. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236
open PASoundness.M236.Control

/-- Exact finite-graph condition expressed in Lean's logic. -/
def RowCorrect (i : Nat) : Prop :=
  match sourceRows[i]?, paths[i]? with
  | some (op, dest, extra), some word =>
    let target := paths[dest]?
    target.isSome = true ∧
    match Continue.pathName 157 word with
    | some "_continue.1" => op = "jump" ∧ extra = none ∧ resolveWith (Continue.restartPrefix 1) word = target
    | some "_continue.2" => op = "jump" ∧ extra = none ∧ resolveWith (Continue.restartPrefix 2) word = target
    | some "_continue.3" => op = "jump" ∧ extra = none ∧ resolveWith (Continue.restartPrefix 3) word = target
    | some "_break.1" => op = "jump" ∧ extra = none ∧ resolveWith (Break.successorPrefix 1) word = target
    | some "_break.3" => op = "jump" ∧ extra = none ∧ resolveWith (Break.successorPrefix 3) word = target
    | some "emit.0" => op = "emit.0" ∧ extra = none ∧ resolveWith (Break.successorPrefix 0) word = target
    | some "emit.1" => op = "emit.1" ∧ extra = none ∧ resolveWith (Break.successorPrefix 0) word = target
    | some name => op = name ∧ dest = (i+1)%760 ∧
      if isDec name then
        match Control.decodeZero word, extra with
        | some (_, tail), some z => paths[z]?.isSome = true ∧ Control.resolveZeros Grammar.nodes 158 157 tail = paths[z]?
        | _, _ => False
      else extra = none
    | none => False
  | _, _ => False

theorem rowMatches_sound (i : Nat) (h : rowMatches i = true) : RowCorrect i := by
  unfold rowMatches RowCorrect at *
  cases hr : sourceRows[i]? with
  | none => simp [hr] at h
  | some row =>
    rcases row with ⟨op, dest, extra⟩
    cases hw : paths[i]? with
    | none => simp [hr, hw] at h
    | some word =>
      cases hn : Continue.pathName 157 word with
      | none => simp [hr, hw, hn] at h
      | some name =>
        by_cases h0 : name = "_continue.1"
        · subst name; simpa [hr, hw, hn, and_assoc] using h
        by_cases h1 : name = "_continue.2"
        · subst name; simpa [hr, hw, hn, and_assoc] using h
        by_cases h2 : name = "_continue.3"
        · subst name; simpa [hr, hw, hn, and_assoc] using h
        by_cases h3 : name = "_break.1"
        · subst name; simpa [hr, hw, hn, and_assoc] using h
        by_cases h4 : name = "_break.3"
        · subst name; simpa [hr, hw, hn, and_assoc] using h
        by_cases h5 : name = "emit.0"
        · subst name; simpa [hr, hw, hn, and_assoc] using h
        by_cases h6 : name = "emit.1"
        · subst name; simpa [hr, hw, hn, and_assoc] using h
        simp only [hr, hw, hn, h0, h1, h2, h3, h4, h5, h6] at h ⊢
        cases hz : isDec name <;> cases hd : decodeZero word <;> cases he : extra <;>
          simp_all [and_assoc] <;> omega
/-- Every retained occurrence row satisfies the explicit logical
operation and destination conditions for the literal grammar. -/
theorem every_occurrence_correct (i : Nat) (hi : i < 760) : RowCorrect i :=
  rowMatches_sound i (every_occurrence_checked i hi)
end PASoundness.M236.OccurrenceGraph
