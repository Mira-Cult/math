import PASoundness.M236BlankThird
import PASoundness.M236SkipSuccessor
/-! A fourth named zero decrement on the literal blank-start execution. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.BlankFirst
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def word4 : List Bool := [false, false, true, true, false, false, false, true, false]
def r4 : Fin 9 := 8
def tail3 : List Bool := [false, false, true, true, false, false, false, true]

theorem path4 : Preparation.NamedPath Grammar.nodes 157 word4
    (.leaf ("3." ++ Selector.registerNames[r4] ++ ".decnz") (DecrementSelector.entryState r4) false .right none) := by
  apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
  apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
  apply Preparation.NamedPath.step 31 30 true _ _ (by decide)
  apply Preparation.NamedPath.step 30 29 true _ _ (by decide)
  apply Preparation.NamedPath.step 29 24 false _ _ (by decide)
  apply Preparation.NamedPath.step 24 21 false _ _ (by decide)
  apply Preparation.NamedPath.step 21 14 false _ _ (by decide)
  apply Preparation.NamedPath.step 14 13 true _ _ (by decide)
  exact Preparation.NamedPath.leaf 13 false _ (by decide) ⟨_, _, _, _, _, rfl⟩

theorem decode3 : Control.decodeZero word3 = some (false, tail3) := by decide

theorem payload4 : Redispatch.selectedPayload zeros r4 reserve [] =
    bank (UnaryNine.values zeros ++ reserve) ++ [false] := by decide

theorem fourth_right (padding : Nat) :
    word4 ++ false :: false :: (List.replicate padding false ++ true :: false ::
      Redispatch.selectedPayload zeros r4 reserve []) =
    tail3 ++ (List.replicate (padding + 3) false ++ true :: false ::
      (bank (UnaryNine.values zeros ++ reserve) ++ [false])) := by
  rw [payload4]
  simp [word4, tail3, List.replicate_succ, List.append_assoc]

/-- The third return has the computed control bits on the same raw execution. -/
theorem third_zero_control_raw :
    ∃ (time1 time2 time3 : Nat) (endHead : Int) (scratch1 scratch2 : Nat),
      0 < time1 ∧ 0 < time2 ∧ 0 < time3 ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ []),
          tail3 ++ (List.replicate (3810 + (scratch2 + scratch1 + 3)) false ++ true :: false ::
            (bank (UnaryNine.values zeros ++ reserve) ++ [false]))⟩⟩
        ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3)) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + time1 + time2 + time3) = [] := by
  obtain ⟨time1, time2, time3, head, scratch1, scratch2, bit, pcTail,
    ht1, ht2, ht3, hdec, hr, ho⟩ := third_zero_control_from_blank
  rw [decode3] at hdec
  cases hdec
  have hm : mapConfig ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3)) =
      (machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3) := by
    rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  rw [← hm] at hr
  obtain ⟨hs, hh, tape⟩ := hr
  have he : ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3)).state = 79 :=
    root_unique_preimage _ hs.symm
  exact ⟨time1, time2, time3, head, scratch1, scratch2, ht1, ht2, ht3, ⟨he.symm, hh, tape⟩, ho⟩
def tail4 : List Bool := [false, false, true, true, false, false, true]
theorem decode4 : Control.decodeZero word4 = some (false, tail4) := by decide

/-- The same literal blank execution performs the fourth named zero branch,
for k.c, and returns with the computed control word and no output. -/
theorem fourth_zero_control_from_blank :
    ∃ (time1 time2 time3 time4 : Nat) (endHead : Int)
      (scratch1 scratch2 scratch3 scratch4 : Nat),
      0 < time1 ∧ 0 < time2 ∧ 0 < time3 ∧ 0 < time4 ∧
      Related ⟨78, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ []),
          tail4 ++ (List.replicate ((3810 + (scratch2 + scratch1)) + (scratch4 + scratch3 + 3)) false ++
            true :: false :: (bank (UnaryNine.values zeros ++ reserve) ++ [false]))⟩⟩
        ((machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3 + time4)) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + time1 + time2 + time3 + time4) = [] := by
  obtain ⟨time1, time2, time3, head, scratch1, scratch2, ht1, ht2, ht3, hr, ho⟩ := third_zero_control_raw
  let padding := 3810 + (scratch2 + scratch1)
  have hpad : 3810 + (scratch2 + scratch1 + 3) = padding + 3 := by dsimp [padding]; omega
  have hr' : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: []),
        word4 ++ false :: false :: (List.replicate padding false ++ true :: false ::
          Redispatch.selectedPayload zeros r4 reserve [])⟩⟩
      ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3)) := by
    have hl : List.replicate 6 false ++ false :: [] = List.replicate 7 false ++ [] := by decide
    rw [fourth_right, hl, ← hpad]
    exact hr
  obtain ⟨time4, endHead, scratch3, scratch4, bit, pcTail, finish, hdec, ht4, hp, hr4, hq, hd, hout⟩ :=
    Control.physical_root_zero_decoded zeros r4 (by rfl) reserve padding word4 false path4 head [] []
      ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3)) hr'
  rw [decode4] at hdec
  cases hdec
  have hstart : mapConfig ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3)) =
      (machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3) := by
    rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  have hend : (machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3 + time4) = mapConfig finish := by
    rw [WordEventSystem.run_add, ← hstart]
    exact hq.endpoint
  have houtput : (machineWordSystem machine machineLabels).prefixWord (89821408 + time1 + time2 + time3 + time4) = [] := by
    rw [WordEventSystem.prefix_add, ← hstart, hq.output, ho]
    rfl
  have hrel := FastBootstrap.Certificate.related_map hr4
  have hqstate : mapState 79 = 78 := by decide
  change Related ⟨mapState 79, endHead, _⟩ _ at hrel
  rw [hqstate] at hrel
  refine ⟨time1, time2, time3, time4, endHead, scratch1, scratch2, scratch3, scratch4, ht1, ht2, ht3, ht4, ?_, houtput⟩
  rw [hend]
  simpa [padding] using hrel
end PASoundness.M236.BlankFirst
