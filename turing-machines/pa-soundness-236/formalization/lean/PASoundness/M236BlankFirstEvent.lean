import PASoundness.M236BlankSixth
import PASoundness.M236EmitCoverage
/-! The first emitted bit on the literal blank-start execution. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.BlankFirst
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def tail7 : List Bool := tail6 ++ [true]

theorem path7 : Preparation.NamedPath Grammar.nodes 157 (tail6 ++ [false])
    (.leaf (Emit.emitName true) 72 true .left (some true)) := by
  apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
  apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
  apply Preparation.NamedPath.step 31 30 true _ _ (by decide)
  apply Preparation.NamedPath.step 30 29 true _ _ (by decide)
  apply Preparation.NamedPath.step 29 24 false _ _ (by decide)
  apply Preparation.NamedPath.step 24 21 false _ _ (by decide)
  apply Preparation.NamedPath.step 21 20 true _ _ (by decide)
  apply Preparation.NamedPath.step 20 19 true _ _ (by decide)
  apply Preparation.NamedPath.step 19 16 false _ _ (by decide)
  apply Preparation.NamedPath.step 16 15 true _ _ (by decide)
  exact Preparation.NamedPath.leaf 15 false _ (by decide) ⟨_, _, _, _, _, rfl⟩

theorem candidate7 : Emit.continueCandidate tail6 =
    some (0, ([1, 0, 2, 0, 3, 0] : List (Fin 6)), false, tail7) := by decide

theorem seventh_right (padding : Nat) (tail : List Bool) :
    (tail6 ++ [false]) ++ (List.replicate padding false ++ true :: false :: tail) =
    tail6 ++ (List.replicate (padding + 1) false ++ true :: false :: tail) := by
  simp [List.replicate_succ, List.append_assoc]

/-- The sixth selected return lifts to the raw table at the same blank-run time. -/
theorem sixth_positive_control_raw :
    ∃ (time1 time2 time3 time4 time5 time6 : Nat) (endHead : Int)
      (scratch1 scratch2 scratch3 scratch4 scratch5 scratch6 : Nat),
      0 < time1 ∧ 0 < time2 ∧ 0 < time3 ∧ 0 < time4 ∧ 0 < time5 ∧ 0 < time6 ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ []),
          tail6 ++ (List.replicate
            (((3808 + (scratch2 + scratch1)) + (scratch4 + scratch3) + scratch5) + scratch6 + 2) false ++
            true :: false :: (bank ([0, 0, 0, 0, 0, 0, 0, 0, 0] ++ (reserve ++ [0]))))⟩⟩
        ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4 + time5 + time6)) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (89821408 + time1 + time2 + time3 + time4 + time5 + time6) = [] := by
  obtain ⟨time1, time2, time3, time4, time5, time6, head, scratch1, scratch2, scratch3, scratch4, scratch5, scratch6,
    ht1, ht2, ht3, ht4, ht5, ht6, hr, ho⟩ := sixth_positive_control_from_blank
  have hm : mapConfig ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4 + time5 + time6)) =
      (machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3 + time4 + time5 + time6) := by
    rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  rw [← hm] at hr
  obtain ⟨hs, hh, tape⟩ := hr
  have he : ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4 + time5 + time6)).state = 79 :=
    root_unique_preimage _ hs.symm
  exact ⟨time1, time2, time3, time4, time5, time6, head, scratch1, scratch2, scratch3, scratch4, scratch5, scratch6,
    ht1, ht2, ht3, ht4, ht5, ht6, ⟨he.symm, hh, tape⟩, ho⟩
/-- On the literal blank-start run, the first emitted bit is true. The prior
prefix is empty and the full prefix at the following root return is [true]. -/
theorem first_event_from_blank :
    ∃ (time1 time2 time3 time4 time5 time6 time7 : Nat) (endHead : Int)
      (scratch1 scratch2 scratch3 scratch4 scratch5 scratch6 : Nat),
      0 < time1 ∧ 0 < time2 ∧ 0 < time3 ∧ 0 < time4 ∧ 0 < time5 ∧ 0 < time6 ∧ 0 < time7 ∧
      (machineWordSystem machine machineLabels).prefixWord
        (89821408 + time1 + time2 + time3 + time4 + time5 + time6) = [] ∧
      Related ⟨78, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ []),
          tail7 ++ (List.replicate
            (((3808 + (scratch2 + scratch1)) + (scratch4 + scratch3) + scratch5) + scratch6 + 1) false ++
            true :: false :: (bank ([0, 0, 0, 0, 0, 0, 0, 0, 0] ++ (reserve ++ [0]))))⟩⟩
        ((machineWordSystem machine machineLabels).run
          (89821408 + time1 + time2 + time3 + time4 + time5 + time6 + time7)) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (89821408 + time1 + time2 + time3 + time4 + time5 + time6 + time7) = [true] := by
  obtain ⟨time1, time2, time3, time4, time5, time6, head, scratch1, scratch2, scratch3, scratch4, scratch5, scratch6,
    ht1, ht2, ht3, ht4, ht5, ht6, hr, ho⟩ := sixth_positive_control_raw
  let padding := ((3808 + (scratch2 + scratch1)) + (scratch4 + scratch3) + scratch5) + scratch6 + 1
  have hpad : ((3808 + (scratch2 + scratch1)) + (scratch4 + scratch3) + scratch5) + scratch6 + 2 = padding + 1 := by
    dsimp [padding]
  have hr' : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ []),
        (tail6 ++ [false]) ++ (List.replicate padding false ++ true :: false ::
          bank ([0, 0, 0, 0, 0, 0, 0, 0, 0] ++ (reserve ++ [0])))⟩⟩
      ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4 + time5 + time6)) := by
    rw [seventh_right, ← hpad]
    exact hr
  obtain ⟨time7, endHead, residual, finish, first, runs, bit, hcan, ht7, hp, hr7, hq⟩ :=
    Emit.physical_covered_continue true tail6 path7 padding head []
      (bank ([0, 0, 0, 0, 0, 0, 0, 0, 0] ++ (reserve ++ [0])))
      ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4 + time5 + time6)) hr'
  rw [candidate7] at hcan
  cases hcan
  have hstart : mapConfig ((machineWordSystem raw rawLabels).run (89821408 + time1 + time2 + time3 + time4 + time5 + time6)) =
      (machineWordSystem machine machineLabels).run (89821408 + time1 + time2 + time3 + time4 + time5 + time6) := by
    rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  have hend : (machineWordSystem machine machineLabels).run
      (89821408 + time1 + time2 + time3 + time4 + time5 + time6 + time7) = mapConfig finish := by
    rw [WordEventSystem.run_add, ← hstart]
    exact hq.endpoint
  have houtput : (machineWordSystem machine machineLabels).prefixWord
      (89821408 + time1 + time2 + time3 + time4 + time5 + time6 + time7) = [true] := by
    rw [WordEventSystem.prefix_add, ← hstart, hq.output, ho]
    rfl
  have hrel := FastBootstrap.Certificate.related_map hr7
  have hqstate : mapState 79 = 78 := by decide
  change Related ⟨mapState 79, endHead, _⟩ _ at hrel
  rw [hqstate] at hrel
  refine ⟨time1, time2, time3, time4, time5, time6, time7, endHead,
    scratch1, scratch2, scratch3, scratch4, scratch5, scratch6,
    ht1, ht2, ht3, ht4, ht5, ht6, ht7, ho, ?_, houtput⟩
  rw [hend]
  simpa [padding] using hrel
end PASoundness.M236.BlankFirst
