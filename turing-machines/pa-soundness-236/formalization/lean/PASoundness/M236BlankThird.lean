import PASoundness.M236BlankSecond
import PASoundness.M236SkipSuccessor
/-! A third named zero decrement on the literal blank-start execution. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.BlankFirst
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def word3 : List Bool := [false, false, true, true, false, false, false, false, false]
def r3 : Fin 9 := 2

theorem root_unique_preimage (q : Fin 237) (h : mapState q = 78) : q = 79 := by
  have : ∀ (q : Fin 237), mapState q = 78 → q = 79 := by decide
  exact this q h

theorem path3 : Preparation.NamedPath Grammar.nodes 157 word3
    (.leaf ("3." ++ Selector.registerNames[r3] ++ ".decnz") (DecrementSelector.entryState r3) false .right none) := by
  apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
  apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
  apply Preparation.NamedPath.step 31 30 true _ _ (by decide)
  apply Preparation.NamedPath.step 30 29 true _ _ (by decide)
  apply Preparation.NamedPath.step 29 24 false _ _ (by decide)
  apply Preparation.NamedPath.step 24 21 false _ _ (by decide)
  apply Preparation.NamedPath.step 21 14 false _ _ (by decide)
  apply Preparation.NamedPath.step 14 11 false _ _ (by decide)
  exact Preparation.NamedPath.leaf 11 false _ (by decide) ⟨_, _, _, _, _, rfl⟩

theorem third_right :
    word3 ++ false :: false :: (List.replicate 3810 false ++ true :: false ::
      Redispatch.selectedPayload zeros r3 reserve []) =
    [false, false, true, true] ++ (List.replicate 3817 false ++ true :: false ::
      (bank (UnaryNine.values zeros ++ reserve) ++ [false])) := by decide

/-- Raw lift of the existing actual blank execution at its second return. -/
theorem second_zero_control_raw :
    ∃ (time1 time2 : Nat) (endHead : Int), 0 < time1 ∧ 0 < time2 ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ []),
          [false, false, true, true] ++ (List.replicate 3817 false ++ true :: false ::
            (bank (UnaryNine.values zeros ++ reserve) ++ [false]))⟩⟩
        ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2)) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + time1 + time2) = [] := by
  obtain ⟨time1, time2, head, ht1, ht2, hr, ho⟩ := second_zero_control_from_blank
  have hm : mapConfig ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2)) =
      (machineWordSystem machine machineLabels).run (89821408 + time1 + time2) := by
    rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  rw [← hm] at hr
  obtain ⟨hs, hh, tape⟩ := hr
  have he : ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2)).state = 79 :=
    root_unique_preimage _ hs.symm
  exact ⟨time1, time2, head, ht1, ht2, ⟨he.symm, hh, tape⟩, ho⟩

/-- The same blank-start execution performs a third, k.rest, zero decrement
and returns silently to the literal grammar root. -/
theorem third_zero_control_from_blank :
    ∃ (time1 time2 time3 : Nat) (endHead : Int) (scratch1 scratch2 : Nat)
      (bit : Bool) (pcTail : List Bool), 0 < time1 ∧ 0 < time2 ∧ 0 < time3 ∧
      Control.decodeZero word3 = some (bit, pcTail) ∧
      Related ⟨78, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ []),
          pcTail ++ (List.replicate (3810 + (scratch2 + scratch1 + 3)) false ++ true :: false ::
            (bank (UnaryNine.values zeros ++ reserve) ++ [false]))⟩⟩
        ((machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3)) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + time1 + time2 + time3) = [] := by
  obtain ⟨time1, time2, head, ht1, ht2, hr, ho⟩ := second_zero_control_raw
  have hr' : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: []),
        word3 ++ false :: false :: (List.replicate 3810 false ++ true :: false ::
          Redispatch.selectedPayload zeros r3 reserve [])⟩⟩
      ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2)) := by
    have hl : List.replicate 6 false ++ false :: [] = List.replicate 7 false ++ [] := by decide
    rw [third_right, hl]
    exact hr
  obtain ⟨time3, endHead, scratch1, scratch2, bit, pcTail, finish, hdec, ht3, hp, hr3, hq, hd, hout⟩ :=
    Control.physical_root_zero_decoded zeros r3 (by rfl) reserve 3810 word3 false path3 head [] []
      ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2)) hr'
  have hstart : mapConfig ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2)) =
      (machineWordSystem machine machineLabels).run (89821408 + time1 + time2) := by
    rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  have hend : (machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3) = mapConfig finish := by
    rw [WordEventSystem.run_add, ← hstart]
    exact hq.endpoint
  have houtput : (machineWordSystem machine machineLabels).prefixWord (89821408 + time1 + time2 + time3) = [] := by
    rw [WordEventSystem.prefix_add, ← hstart, hq.output, ho]
    rfl
  have hrel := FastBootstrap.Certificate.related_map hr3
  have hqstate : mapState 79 = 78 := by decide
  change Related ⟨mapState 79, endHead, _⟩ _ at hrel
  rw [hqstate] at hrel
  refine ⟨time1, time2, time3, endHead, scratch1, scratch2, bit, pcTail, ht1, ht2, ht3, hdec, ?_, houtput⟩
  rw [hend]
  simpa using hrel
end PASoundness.M236.BlankFirst
