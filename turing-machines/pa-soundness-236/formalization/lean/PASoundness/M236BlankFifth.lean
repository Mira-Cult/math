import PASoundness.M236BlankFourth
/-! A named increment after four zero decrements on the literal blank-start execution. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.BlankFirst
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def word5 : List Bool := [false, false, true, true, false, false, true, false]
def r5 : Fin 9 := 6
def tail5 : List Bool := [false, false, true, true, false, false, true, true]

theorem path5 : Preparation.NamedPath Grammar.nodes 157 word5
    (.leaf ("3." ++ Selector.registerNames[r5] ++ ".inc") (Selector.entryState r5) false .right none) := by
  apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
  apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
  apply Preparation.NamedPath.step 31 30 true _ _ (by decide)
  apply Preparation.NamedPath.step 30 29 true _ _ (by decide)
  apply Preparation.NamedPath.step 29 24 false _ _ (by decide)
  apply Preparation.NamedPath.step 24 21 false _ _ (by decide)
  apply Preparation.NamedPath.step 21 20 true _ _ (by decide)
  exact Preparation.NamedPath.leaf 20 false _ (by decide) ⟨_, _, _, _, _, rfl⟩

theorem decode5 : Control.decodeOne word5 = some (false, tail5) := by decide

theorem payload5 : Redispatch.selectedPayload zeros r5 reserve [] =
    bank (UnaryNine.values zeros ++ reserve) ++ [false] := by decide

theorem fifth_right (padding : Nat) :
    word5 ++ false :: false :: (List.replicate padding false ++ true :: false ::
      Redispatch.selectedPayload zeros r5 reserve []) =
    tail4 ++ (List.replicate (padding + 3) false ++ true :: false ::
      (bank (UnaryNine.values zeros ++ reserve) ++ [false])) := by
  rw [payload5]
  simp [word5, tail4, List.replicate_succ, List.append_assoc]

theorem fifth_bank_values :
    UnaryNine.values (RegisterMachine.execute (.inc r5) zeros).bank = [0, 0, 0, 0, 0, 0, 1, 0, 0] := by decide

/-- The fourth return lifts uniquely to the raw execution with its whole tape. -/
theorem fourth_zero_control_raw :
    ∃ (time1 time2 time3 time4 : Nat) (endHead : Int)
      (scratch1 scratch2 scratch3 scratch4 : Nat),
      0 < time1 ∧ 0 < time2 ∧ 0 < time3 ∧ 0 < time4 ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ []),
          tail4 ++ (List.replicate ((3810 + (scratch2 + scratch1)) + (scratch4 + scratch3 + 3)) false ++
            true :: false :: (bank (UnaryNine.values zeros ++ reserve) ++ [false]))⟩⟩
        ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4)) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + time1 + time2 + time3 + time4) = [] := by
  obtain ⟨time1, time2, time3, time4, head, scratch1, scratch2, scratch3, scratch4,
    ht1, ht2, ht3, ht4, hr, ho⟩ := fourth_zero_control_from_blank
  have hm : mapConfig ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4)) =
      (machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3 + time4) := by
    rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  rw [← hm] at hr
  obtain ⟨hs, hh, tape⟩ := hr
  have he : ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4)).state = 79 :=
    root_unique_preimage _ hs.symm
  exact ⟨time1, time2, time3, time4, head, scratch1, scratch2, scratch3, scratch4,
    ht1, ht2, ht3, ht4, ⟨he.symm, hh, tape⟩, ho⟩

/-- After the four zero branches, the actual blank execution increments k.a,
returns to the grammar root, and still has emitted no output. -/
theorem fifth_increment_control_from_blank :
    ∃ (time1 time2 time3 time4 time5 : Nat) (endHead : Int)
      (scratch1 scratch2 scratch3 scratch4 scratch5 : Nat),
      0 < time1 ∧ 0 < time2 ∧ 0 < time3 ∧ 0 < time4 ∧ 0 < time5 ∧
      Related ⟨78, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ []),
          tail5 ++ (List.replicate (((3810 + (scratch2 + scratch1)) + (scratch4 + scratch3)) + scratch5 + 2) false ++
            true :: false :: (bank ([0, 0, 0, 0, 0, 0, 1, 0, 0] ++ reserve)))⟩⟩
        ((machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3 + time4 + time5)) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + time1 + time2 + time3 + time4 + time5) = [] := by
  obtain ⟨time1, time2, time3, time4, head, scratch1, scratch2, scratch3, scratch4,
    ht1, ht2, ht3, ht4, hr, ho⟩ := fourth_zero_control_raw
  let padding := (3810 + (scratch2 + scratch1)) + (scratch4 + scratch3)
  have hpad : (3810 + (scratch2 + scratch1)) + (scratch4 + scratch3 + 3) = padding + 3 := by
    dsimp [padding]; omega
  have hr' : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: []),
        word5 ++ false :: false :: (List.replicate padding false ++ true :: false ::
          Redispatch.selectedPayload zeros r5 reserve [])⟩⟩
      ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4)) := by
    have hl : List.replicate 6 false ++ false :: [] = List.replicate 7 false ++ [] := by decide
    rw [fifth_right, hl, ← hpad]
    exact hr
  obtain ⟨time5, endHead, scratch5, bit, pcTail, finish, hdec, ht5, hp, hr5, hq, hd⟩ :=
    Control.physical_root_increment_decoded zeros r5 reserve padding word5 false path5 head [] []
      ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4)) hr'
  rw [decode5] at hdec
  cases hdec
  have hstart : mapConfig ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4)) =
      (machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3 + time4) := by
    rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  have hend : (machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3 + time4 + time5) = mapConfig finish := by
    rw [WordEventSystem.run_add, ← hstart]
    exact hq.endpoint
  have houtput : (machineWordSystem machine machineLabels).prefixWord (89821408 + time1 + time2 + time3 + time4 + time5) = [] := by
    rw [WordEventSystem.prefix_add, ← hstart, hq.output, ho]
    rfl
  have hrel := FastBootstrap.Certificate.related_map hr5
  have hqstate : mapState 79 = 78 := by decide
  change Related ⟨mapState 79, endHead, _⟩ _ at hrel
  rw [hqstate] at hrel
  refine ⟨time1, time2, time3, time4, time5, endHead, scratch1, scratch2, scratch3, scratch4, scratch5,
    ht1, ht2, ht3, ht4, ht5, ?_, houtput⟩
  rw [hend]
  simpa [padding, fifth_bank_values] using hrel
end PASoundness.M236.BlankFirst
