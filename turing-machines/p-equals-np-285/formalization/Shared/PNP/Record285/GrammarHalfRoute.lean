import Shared.PNP.Record285.OperationInvariant
import Shared.PNP.Record285.GrammarGraph

/-! Every frozen grammar half path is a safe literal dispatcher route. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.Grammar
open Shared.Beeping.Machines
open Shared.PNP.Record285.GenericDispatch

theorem walk_half_route (code : List Bool) (n i : Nat)
    (hwalk : walk n code = some (.half i)) :
    i < 4 ∧ route (state n) code = some (halfTerminal i) := by
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
      | half j =>
        cases bs with
        | nil =>
          simp only [walk,he,List.isEmpty_nil,if_true,Option.some.injEq,Edge.half.injEq] at hwalk
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
      | dec j => cases bs <;> simp [walk,he] at hwalk
      | beep => cases bs <;> simp [walk,he] at hwalk
      | brk j => cases bs <;> simp [walk,he] at hwalk
      | cont j => cases bs <;> simp [walk,he] at hwalk

theorem root_half_route (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.half i)) :
    i < 4 ∧ route treeRoot code = some (halfTerminal i) := by
  have h := walk_half_route code 162 i hwalk
  simpa only [root_state] using h

theorem producer_half_safe (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.half i)) :
    i < 4 ∧ route treeRoot code = some (halfTerminal i) ∧
      detectorRun 0 (scanWord code) = some 0 := by
  have hr := root_half_route code i hwalk
  exact ⟨hr.1,hr.2,OperationInvariant.half_route_safe code i hr.1 hr.2⟩

end Shared.PNP.Record285.Grammar
