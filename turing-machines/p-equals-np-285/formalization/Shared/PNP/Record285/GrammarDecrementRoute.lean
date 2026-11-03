import Shared.PNP.Record285.OperationInvariant
import Shared.PNP.Record285.GrammarGraph

/-! Every frozen grammar decrement path is a safe literal dispatcher route. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.Grammar
open Shared.Beeping.Machines
open Shared.PNP.Record285.GenericDispatch

theorem walk_decrement_route (code : List Bool) (n i : Nat)
    (hwalk : walk n code = some (.dec i)) :
    i < 15 ∧ route (state n) code = some (decTerminal i) := by
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
      | dec j =>
        cases bs with
        | nil =>
          simp only [walk,he,List.isEmpty_nil,if_true,Option.some.injEq,Edge.dec.injEq] at hwalk
          subst j
          simp only [expected] at hget
          split at hget
          next hj =>
            simp only [Option.some.injEq] at hget
            rw [← hget] at hrow
            exact ⟨hj, by simp [route,hrow]⟩
          next hj => contradiction
        | cons x xs => simp [walk,he] at hwalk
      | inc j => cases bs <;> simp [walk,he] at hwalk
      | half j => cases bs <;> simp [walk,he] at hwalk
      | beep => cases bs <;> simp [walk,he] at hwalk
      | brk j => cases bs <;> simp [walk,he] at hwalk
      | cont j => cases bs <;> simp [walk,he] at hwalk

theorem root_decrement_route (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.dec i)) :
    i < 15 ∧ route treeRoot code = some (decTerminal i) := by
  have h := walk_decrement_route code 162 i hwalk
  simpa only [root_state] using h

theorem producer_decrement_safe (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.dec i)) :
    i < 15 ∧ route treeRoot code = some (decTerminal i) ∧
      detectorRun 0 (scanWord code) = some 0 := by
  have hr := root_decrement_route code i hwalk
  exact ⟨hr.1,hr.2,OperationInvariant.dec_route_safe code i hr.1 hr.2⟩

end Shared.PNP.Record285.Grammar
