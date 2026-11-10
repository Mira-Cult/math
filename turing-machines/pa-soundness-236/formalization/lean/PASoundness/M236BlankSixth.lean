import PASoundness.M236BlankFifth
/-! A positive named decrement after the increment on the literal blank run. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.BlankFirst
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def word6 : List Bool := [false, false, true, true, false, false, true, true, false, false]
def tail6 : List Bool := [false, false, true, true, false, false, true, true, false, true]
def bank5 : RegisterMachine.Bank 9 := (RegisterMachine.execute (.inc r5) zeros).bank

theorem path6 : Preparation.NamedPath Grammar.nodes 157 word6
    (.leaf ("3." ++ Selector.registerNames[r5] ++ ".decnz") (DecrementSelector.entryState r5) false .right none) := by
  apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
  apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
  apply Preparation.NamedPath.step 31 30 true _ _ (by decide)
  apply Preparation.NamedPath.step 30 29 true _ _ (by decide)
  apply Preparation.NamedPath.step 29 24 false _ _ (by decide)
  apply Preparation.NamedPath.step 24 21 false _ _ (by decide)
  apply Preparation.NamedPath.step 21 20 true _ _ (by decide)
  apply Preparation.NamedPath.step 20 19 true _ _ (by decide)
  apply Preparation.NamedPath.step 19 16 false _ _ (by decide)
  exact Preparation.NamedPath.leaf 16 false _ (by decide) ⟨_, _, _, _, _, rfl⟩

theorem decode6 : Control.decodeOne word6 = some (false, tail6) := by decide

theorem bank5_selected : bank5 r5 = 0 + 1 := by decide

theorem sixth_bank_values :
    UnaryNine.values (RegisterMachine.execute (.decNZ r5) bank5).bank = [0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide

theorem payload6 : Redispatch.selectedPayload bank5 r5 reserve [] =
    bank ([0, 0, 0, 0, 0, 0, 1, 0, 0] ++ reserve) ++ [false] := by decide

theorem sixth_right (padding : Nat) :
    word6 ++ false :: false :: (List.replicate padding false ++ true :: false ::
      Redispatch.selectedPayload bank5 r5 reserve []) =
    (tail5 ++ (List.replicate (padding + 4) false ++ true :: false ::
      bank ([0, 0, 0, 0, 0, 0, 1, 0, 0] ++ reserve))) ++ [false] := by
  rw [payload6]
  simp [word6, tail5, List.replicate_succ, List.append_assoc]

/-- Adding one trailing zero to the right zipper preserves the full physical tape. -/
theorem related_append_false {q : Fin 237} {head : Int} {left right : List Bool} {c : Config 237}
    (h : Related ⟨q, head, ⟨left, right⟩⟩ c) :
    Related ⟨q, head, ⟨left, right ++ [false]⟩⟩ c := by
  obtain ⟨hs, hh, hr, hl⟩ := h
  refine ⟨hs, hh, ?_, hl⟩
  intro i
  rw [getD_append_false]
  exact hr i

/-- The fifth selected return has the unique raw root preimage on the same run. -/
theorem fifth_increment_control_raw :
    ∃ (time1 time2 time3 time4 time5 : Nat) (endHead : Int)
      (scratch1 scratch2 scratch3 scratch4 scratch5 : Nat),
      0 < time1 ∧ 0 < time2 ∧ 0 < time3 ∧ 0 < time4 ∧ 0 < time5 ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ []),
          tail5 ++ (List.replicate (((3810 + (scratch2 + scratch1)) + (scratch4 + scratch3)) + scratch5 + 2) false ++
            true :: false :: (bank ([0, 0, 0, 0, 0, 0, 1, 0, 0] ++ reserve)))⟩⟩
        ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4 + time5)) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + time1 + time2 + time3 + time4 + time5) = [] := by
  obtain ⟨time1, time2, time3, time4, time5, head, scratch1, scratch2, scratch3, scratch4, scratch5,
    ht1, ht2, ht3, ht4, ht5, hr, ho⟩ := fifth_increment_control_from_blank
  have hm : mapConfig ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4 + time5)) =
      (machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3 + time4 + time5) := by
    rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  rw [← hm] at hr
  obtain ⟨hs, hh, tape⟩ := hr
  have he : ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4 + time5)).state = 79 :=
    root_unique_preimage _ hs.symm
  exact ⟨time1, time2, time3, time4, time5, head, scratch1, scratch2, scratch3, scratch4, scratch5,
    ht1, ht2, ht3, ht4, ht5, ⟨he.symm, hh, tape⟩, ho⟩
/-- The actual blank run takes the positive k.a decrement after the increment,
restores all nine register values to zero, and adds one zero reserve block. -/
theorem sixth_positive_control_from_blank :
    ∃ (time1 time2 time3 time4 time5 time6 : Nat) (endHead : Int)
      (scratch1 scratch2 scratch3 scratch4 scratch5 scratch6 : Nat),
      0 < time1 ∧ 0 < time2 ∧ 0 < time3 ∧ 0 < time4 ∧ 0 < time5 ∧ 0 < time6 ∧
      Related ⟨78, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ []),
          tail6 ++ (List.replicate
            (((3808 + (scratch2 + scratch1)) + (scratch4 + scratch3) + scratch5) + scratch6 + 2) false ++
            true :: false :: (bank ([0, 0, 0, 0, 0, 0, 0, 0, 0] ++ (reserve ++ [0]))))⟩⟩
        ((machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3 + time4 + time5 + time6)) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (89821408 + time1 + time2 + time3 + time4 + time5 + time6) = [] := by
  obtain ⟨time1, time2, time3, time4, time5, head, scratch1, scratch2, scratch3, scratch4, scratch5,
    ht1, ht2, ht3, ht4, ht5, hr, ho⟩ := fifth_increment_control_raw
  let padding := (3808 + (scratch2 + scratch1)) + (scratch4 + scratch3) + scratch5
  have hpad : ((3810 + (scratch2 + scratch1)) + (scratch4 + scratch3)) + scratch5 + 2 = padding + 4 := by
    dsimp [padding]; omega
  have hrAdded := related_append_false hr
  have hr' : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: []),
        word6 ++ false :: false :: (List.replicate padding false ++ true :: false ::
          Redispatch.selectedPayload bank5 r5 reserve [])⟩⟩
      ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4 + time5)) := by
    have hl : List.replicate 6 false ++ false :: [] = List.replicate 7 false ++ [] := by decide
    rw [sixth_right, hl, ← hpad]
    exact hrAdded
  obtain ⟨time6, endHead, scratch6, bit, pcTail, finish, hdec, ht6, hp, hr6, hq, hd, hout⟩ :=
    Control.physical_root_positive_decoded bank5 r5 0 bank5_selected reserve padding word6 false path6 head [] []
      ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4 + time5)) hr'
  rw [decode6] at hdec
  cases hdec
  have hstart : mapConfig ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4 + time5)) =
      (machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3 + time4 + time5) := by
    rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  have hend : (machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3 + time4 + time5 + time6) = mapConfig finish := by
    rw [WordEventSystem.run_add, ← hstart]
    exact hq.endpoint
  have houtput : (machineWordSystem machine machineLabels).prefixWord
      (89821408 + time1 + time2 + time3 + time4 + time5 + time6) = [] := by
    rw [WordEventSystem.prefix_add, ← hstart, hq.output, ho]
    rfl
  have hrel := FastBootstrap.Certificate.related_map hr6
  have hqstate : mapState 79 = 78 := by decide
  change Related ⟨mapState 79, endHead, _⟩ _ at hrel
  rw [hqstate] at hrel
  refine ⟨time1, time2, time3, time4, time5, time6, endHead, scratch1, scratch2, scratch3, scratch4, scratch5, scratch6,
    ht1, ht2, ht3, ht4, ht5, ht6, ?_, houtput⟩
  rw [hend]
  simpa [padding, sixth_bank_values] using hrel
end PASoundness.M236.BlankFirst
