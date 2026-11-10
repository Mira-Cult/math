import PASoundness.M236Restart
import PASoundness.M236Candidate
/-! Prepared physical continue returns aligned with literal restart destinations. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Continue
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

theorem physical_restart_continue1 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.1" 72 false .left none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left), (pre ++ [last]) ++ tail⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual source next : List Bool) (finish : Config 237) (first : Nat) (runs : List (Fin 6)) (bit : Bool),
      candidate1 pre = some (first, runs, bit, residual) ∧
      restartPrefix 1 (pre ++ [last]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next ∧
      Grammar.LeafPath Grammar.nodes 157 next ∧
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), residual ++ tail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  obtain ⟨first, runs, bit, residual, hcan, hs, hc⟩ := candidate1_data pre last hpath
  obtain ⟨source, next, hsource, hnext1, hnext2⟩ := restart1_destination pre last hpath first runs bit residual hcan
  have hstack : pre.reverse ++ (false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate first false ++ true ::
        (counterWord runs ++ List.replicate 6 false ++ false :: left) := by
    have h := congrArg (fun xs : List Bool => xs ++ (List.replicate 7 false ++ left)) hs
    simpa [stack, List.append_assoc, List.replicate_succ] using h
  have hroot : counterPush runs (List.replicate first false ++ false :: tail) =
      true :: bit :: (residual ++ tail) := by
    have h := counterPush_append runs (suffix1 first) tail
    rw [hc] at h
    simpa [suffix1, List.append_assoc] using h
  obtain ⟨finish, hp, hr, hq, ht1, ht2⟩ := physical_named_continue1_to_root pre last hpath
    first runs bit (residual ++ tail) head (false :: true :: true :: (List.replicate 7 false ++ left))
    left tail c hstack hroot hrel
  exact ⟨_, _, residual, source, next, finish, first, runs, bit, hcan, hsource, hnext1, hnext2,
    Control.resolveZeros_sound Grammar.nodes 158 157 source next hnext1, by omega, hp, hr, hq⟩

theorem physical_restart_continue2 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.2" 73 false .left none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left), (pre ++ [last]) ++ tail⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual source next : List Bool) (finish : Config 237) (first second : Nat) (runs : List (Fin 6)) (bit : Bool),
      candidate2 pre = some (first, second, runs, bit, residual) ∧
      restartPrefix 2 (pre ++ [last]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next ∧
      Grammar.LeafPath Grammar.nodes 157 next ∧
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), residual ++ tail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  obtain ⟨first, second, runs, bit, residual, hcan, hs, hc⟩ := candidate2_data pre last hpath
  obtain ⟨source, next, hsource, hnext1, hnext2⟩ := restart2_destination pre last hpath first second runs bit residual hcan
  have hstack : pre.reverse ++ (false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate first false ++ true :: (List.replicate second false ++ true ::
        (counterWord runs ++ List.replicate 6 false ++ false :: left)) := by
    have h := congrArg (fun xs : List Bool => xs ++ (List.replicate 7 false ++ left)) hs
    simpa [stack, List.append_assoc, List.replicate_succ] using h
  have hroot : counterPush runs (List.replicate second false ++ false ::
      (List.replicate first false ++ false :: tail)) = true :: bit :: (residual ++ tail) := by
    have h := counterPush_append runs (suffix2 first second) tail
    rw [hc] at h
    simpa [suffix1, suffix2, List.append_assoc] using h
  obtain ⟨finish, hp, hr, hq, ht1, ht2⟩ := physical_named_continue2_to_root pre last hpath
    first second runs bit (residual ++ tail) head (false :: true :: true :: (List.replicate 7 false ++ left))
    left tail c hstack hroot hrel
  exact ⟨_, _, residual, source, next, finish, first, second, runs, bit, hcan, hsource, hnext1, hnext2,
    Control.resolveZeros_sound Grammar.nodes 158 157 source next hnext1, by omega, hp, hr, hq⟩

theorem physical_restart_continue3 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.3" 74 false .left none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left), (pre ++ [last]) ++ tail⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual source next : List Bool) (finish : Config 237) (first second third : Nat) (runs : List (Fin 6)) (bit : Bool),
      candidate3 pre = some (first, second, third, runs, bit, residual) ∧
      restartPrefix 3 (pre ++ [last]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next ∧
      Grammar.LeafPath Grammar.nodes 157 next ∧
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), residual ++ tail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  obtain ⟨first, second, third, runs, bit, residual, hcan, hs, hc⟩ := candidate3_data pre last hpath
  obtain ⟨source, next, hsource, hnext1, hnext2⟩ := restart3_destination pre last hpath first second third runs bit residual hcan
  have hstack : pre.reverse ++ (false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate first false ++ true :: (List.replicate second false ++ true ::
        (List.replicate third false ++ true :: (counterWord runs ++ List.replicate 6 false ++ false :: left))) := by
    have h := congrArg (fun xs : List Bool => xs ++ (List.replicate 7 false ++ left)) hs
    simpa [stack, List.append_assoc, List.replicate_succ] using h
  have hroot : counterPush runs (List.replicate third false ++ false ::
      (List.replicate second false ++ false :: (List.replicate first false ++ false :: tail))) =
      true :: bit :: (residual ++ tail) := by
    have h := counterPush_append runs (suffix3 first second third) tail
    rw [hc] at h
    simpa [suffix1, suffix2, suffix3, List.append_assoc] using h
  obtain ⟨finish, hp, hr, hq, ht1, ht2⟩ := physical_named_continue3_to_root pre last hpath
    first second third runs bit (residual ++ tail) head (false :: true :: true :: (List.replicate 7 false ++ left))
    left tail c hstack hroot hrel
  exact ⟨_, _, residual, source, next, finish, first, second, third, runs, bit, hcan, hsource, hnext1, hnext2,
    Control.resolveZeros_sound Grammar.nodes 158 157 source next hnext1, by omega, hp, hr, hq⟩
end PASoundness.M236.Continue
