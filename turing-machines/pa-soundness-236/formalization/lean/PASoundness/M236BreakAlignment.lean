import PASoundness.M236BreakSuccessor
/-! Prepared break returns aligned with literal successor destinations. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Break
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

theorem physical_successor_break1 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.1" 69 false .left none))
    (gap : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual source next : List Bool) (finish : Config 237) (first scratch : Nat) (runs : List (Fin 6)) (bit : Bool),
      candidate1 pre = some (first, scratch, runs, bit, residual) ∧
      successorPrefix 1 (pre ++ [last]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next ∧
      Grammar.LeafPath Grammar.nodes 157 next ∧
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          residual ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  obtain ⟨first, scratch, runs, bit, residual, hcan, hs, hc⟩ := candidate1_data pre last hpath
  obtain ⟨source, next, hsource, hnext1, hnext2⟩ := successor1_destination pre last hpath first scratch runs bit residual hcan
  have hstack : pre.reverse ++ (false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate first true ++ false :: (List.replicate scratch true ++ false ::
        (counterWord runs ++ List.replicate 6 false ++ false :: left)) := by
    have h := congrArg (fun xs : List Bool => xs ++ (List.replicate 7 false ++ left)) hs
    simpa [Continue.stack, List.append_assoc, List.replicate_succ] using h
  have hroot : counterPush runs
      (List.replicate (scratch + 1 + (first + 1 + gap)) false ++ true :: false :: tail) =
      true :: bit :: (residual ++ (List.replicate gap false ++ true :: false :: tail)) := by
    have hn : scratch + 1 + (first + 1 + gap) = base1 first scratch + gap := by dsimp [base1]; omega
    rw [hn, ← List.replicate_append_replicate, List.append_assoc]
    have h := counterPush_append runs (List.replicate (base1 first scratch) false)
      (List.replicate gap false ++ true :: false :: tail)
    rw [hc] at h
    exact h
  obtain ⟨finish, hp, hr, hq, ht1, ht2⟩ := physical_named_break1_to_root pre last hpath first scratch gap runs bit
    (residual ++ (List.replicate gap false ++ true :: false :: tail)) head
    (false :: true :: true :: (List.replicate 7 false ++ left)) left tail c hstack hroot hrel
  exact ⟨_, _, residual, source, next, finish, first, scratch, runs, bit, hcan, hsource, hnext1, hnext2,
    Control.resolveZeros_sound Grammar.nodes 158 157 source next hnext1, by omega, hp, hr, hq⟩

theorem physical_successor_break3 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.3" 71 false .left none))
    (gap : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual source next : List Bool) (finish : Config 237) (first second third scratch : Nat) (runs : List (Fin 6)) (bit : Bool),
      candidate3 pre = some (first, second, third, scratch, runs, bit, residual) ∧
      successorPrefix 3 (pre ++ [last]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next ∧
      Grammar.LeafPath Grammar.nodes 157 next ∧
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          residual ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  obtain ⟨first, second, third, scratch, runs, bit, residual, hcan, hs, hc⟩ := candidate3_data pre last hpath
  obtain ⟨source, next, hsource, hnext1, hnext2⟩ := successor3_destination pre last hpath first second third scratch runs bit residual hcan
  have hstack : pre.reverse ++ (false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate first true ++ false :: (List.replicate second true ++ false ::
        (List.replicate third true ++ false :: (List.replicate scratch true ++ false ::
          (counterWord runs ++ List.replicate 6 false ++ false :: left)))) := by
    have h := congrArg (fun xs : List Bool => xs ++ (List.replicate 7 false ++ left)) hs
    simpa [Continue.stack, List.append_assoc, List.replicate_succ] using h
  have hroot : counterPush runs
      (List.replicate (scratch + 1 + (third + 1 + (second + 1 + (first + 1 + gap)))) false ++
        true :: false :: tail) = true :: bit :: (residual ++ (List.replicate gap false ++ true :: false :: tail)) := by
    have hn : scratch + 1 + (third + 1 + (second + 1 + (first + 1 + gap))) =
        base3 first second third scratch + gap := by dsimp [base3]; omega
    rw [hn, ← List.replicate_append_replicate, List.append_assoc]
    have h := counterPush_append runs (List.replicate (base3 first second third scratch) false)
      (List.replicate gap false ++ true :: false :: tail)
    rw [hc] at h
    exact h
  obtain ⟨finish, hp, hr, hq, ht1, ht2⟩ := physical_named_break3_to_root pre last hpath
    first second third scratch gap runs bit (residual ++ (List.replicate gap false ++ true :: false :: tail)) head
    (false :: true :: true :: (List.replicate 7 false ++ left)) left tail c hstack hroot hrel
  exact ⟨_, _, residual, source, next, finish, first, second, third, scratch, runs, bit, hcan, hsource, hnext1, hnext2,
    Control.resolveZeros_sound Grammar.nodes 158 157 source next hnext1, by omega, hp, hr, hq⟩
end PASoundness.M236.Break
