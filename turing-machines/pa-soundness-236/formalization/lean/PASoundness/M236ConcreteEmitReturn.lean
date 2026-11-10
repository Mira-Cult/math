import PASoundness.M236EmitReturn
/-! Concrete marked root paths followed by their exact silent returns. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Emit
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def pre0 : List Bool := [false, true, false, false, true, true, true]
def runs0 : List (Fin 6) := [0, 0, 2, 2, 0]
def control0 : List Bool := [false, true, false, false, true, true, true, true]

theorem path0 : Preparation.NamedPath Grammar.nodes 157 (pre0 ++ [false])
    (.leaf (emitName false) 72 true .left (some false)) := by
  apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
  apply Preparation.NamedPath.step 141 140 true _ _ (by decide)
  apply Preparation.NamedPath.step 140 82 false _ _ (by decide)
  apply Preparation.NamedPath.step 82 36 false _ _ (by decide)
  apply Preparation.NamedPath.step 36 25 true _ _ (by decide)
  apply Preparation.NamedPath.step 25 19 true _ _ (by decide)
  apply Preparation.NamedPath.step 19 18 true _ _ (by decide)
  exact Preparation.NamedPath.leaf 18 false _ (by decide) ⟨_, _, _, _, _, rfl⟩

theorem stack0 (left : List Bool) :
    pre0.reverse ++ (false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate 0 false ++ true :: (counterWord runs0 ++ List.replicate 6 false ++ false :: left) := by
  simp [pre0, runs0, counterWord, List.replicate_succ]

theorem root0 (tail : List Bool) :
    counterPush runs0 (List.replicate 0 false ++ true :: tail) = true :: false :: (control0 ++ tail) := by
  simp [runs0, control0, counterPush, List.replicate_succ]

/-- The zero output path returns to the root in 34 steps on the full tape. -/
theorem physical_emit0_root (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left), (pre0 ++ [false]) ++ tail⟩⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c 34 finish [false] ∧
      Related ⟨79, head, ⟨false :: true :: true :: (List.replicate 7 false ++ left), control0 ++ tail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) 34 (mapConfig finish) [false] := by
  obtain ⟨finish, hp, hr, hq, _, _⟩ := physical_emit_to_root false pre0 false path0 0 runs0 false
    (control0 ++ tail) head (false :: true :: true :: (List.replicate 7 false ++ left)) left tail c
    (stack0 left) (root0 tail) hrel
  refine ⟨finish, ?_, ?_, ?_⟩
  · simpa [pre0, runs0, counterTime] using hp
  · have hh : head + 7 - 1 - 1 - 9 - 6 + 10 = head := by omega
    simpa [pre0, runs0, counterTime, Move.apply, hh] using hr
  · simpa [pre0, runs0, counterTime] using hq
def pre1 : List Bool := [false, true, false, false, true, true, false, true]
def runs1 : List (Fin 6) := [1, 0, 2, 2, 0]
def control1 : List Bool := [false, true, false, false, true, true, false, true, true]

theorem path1 : Preparation.NamedPath Grammar.nodes 157 (pre1 ++ [false])
    (.leaf (emitName true) 72 true .left (some true)) := by
  apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
  apply Preparation.NamedPath.step 141 140 true _ _ (by decide)
  apply Preparation.NamedPath.step 140 82 false _ _ (by decide)
  apply Preparation.NamedPath.step 82 36 false _ _ (by decide)
  apply Preparation.NamedPath.step 36 25 true _ _ (by decide)
  apply Preparation.NamedPath.step 25 19 true _ _ (by decide)
  apply Preparation.NamedPath.step 19 16 false _ _ (by decide)
  apply Preparation.NamedPath.step 16 15 true _ _ (by decide)
  exact Preparation.NamedPath.leaf 15 false _ (by decide) ⟨_, _, _, _, _, rfl⟩

theorem stack1 (left : List Bool) :
    pre1.reverse ++ (false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate 0 false ++ true :: (counterWord runs1 ++ List.replicate 6 false ++ false :: left) := by
  simp [pre1, runs1, counterWord, List.replicate_succ]

theorem root1 (tail : List Bool) :
    counterPush runs1 (List.replicate 0 false ++ true :: tail) = true :: false :: (control1 ++ tail) := by
  simp [runs1, control1, counterPush, List.replicate_succ]

/-- The one output path returns to the root in 36 steps on the full tape. -/
theorem physical_emit1_root (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left), (pre1 ++ [false]) ++ tail⟩⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c 36 finish [true] ∧
      Related ⟨79, head, ⟨false :: true :: true :: (List.replicate 7 false ++ left), control1 ++ tail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) 36 (mapConfig finish) [true] := by
  obtain ⟨finish, hp, hr, hq, _, _⟩ := physical_emit_to_root true pre1 false path1 0 runs1 false
    (control1 ++ tail) head (false :: true :: true :: (List.replicate 7 false ++ left)) left tail c
    (stack1 left) (root1 tail) hrel
  refine ⟨finish, ?_, ?_, ?_⟩
  · simpa [pre1, runs1, counterTime] using hp
  · have hh : head + 8 - 1 - 1 - 10 - 6 + 10 = head := by omega
    simpa [pre1, runs1, counterTime, Move.apply, hh] using hr
  · simpa [pre1, runs1, counterTime] using hq
end PASoundness.M236.Emit
