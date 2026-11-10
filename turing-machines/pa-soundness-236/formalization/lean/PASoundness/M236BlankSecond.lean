import PASoundness.M236FirstPullback
/-! A second finite named decrement on the same literal blank-start run. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.BlankFirst
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def word2 : List Bool := [false, false, true, false, false]
def r2 : Fin 9 := 0

theorem path2 : Preparation.NamedPath Grammar.nodes 157 word2
    (.leaf ("3." ++ Selector.registerNames[r2] ++ ".decnz") (DecrementSelector.entryState r2) false .right none) := by
  apply Preparation.NamedPath.step 157 141 false _ _ (by decide)
  apply Preparation.NamedPath.step 141 31 false _ _ (by decide)
  apply Preparation.NamedPath.step 31 30 true _ _ (by decide)
  apply Preparation.NamedPath.step 30 4 false _ _ (by decide)
  exact Preparation.NamedPath.leaf 4 false _ (by decide) ⟨_, _, _, _, _, rfl⟩

/-- The first return tape has the exact input layout for the next path. -/
theorem second_right :
    word2 ++ false :: false :: (List.replicate 3814 false ++ true :: false ::
      Redispatch.selectedPayload zeros r2 reserve []) =
    [false, false, true] ++ (List.replicate 3818 false ++ true :: false ::
      (bank (UnaryNine.values zeros ++ reserve) ++ [false])) := by decide

/-- This path has a unique scratch split and residual control word. -/
theorem split_word2 (runs rest : List (Fin 6)) (scratch1 scratch2 : Nat) (bit : Bool) (pcTail : List Bool)
    (hw : counterWord runs = [false, false, true, false, false, false, true, true])
    (hs : counterWord runs = List.replicate scratch1 true ++ false ::
      (List.replicate scratch2 true ++ false :: counterWord rest))
    (hp : counterPush rest [] = true :: bit :: pcTail) :
    scratch1 = 0 ∧ scratch2 = 0 ∧ bit = false ∧ pcTail = [false, false, true, true] := by
  rw [hw] at hs
  cases scratch1 with
  | succ n => simp [List.replicate_succ] at hs
  | zero =>
    cases scratch2 with
    | succ n => simp [List.replicate_succ] at hs
    | zero =>
      have hrest : counterWord rest = [true, false, false, false, true, true] := by simpa using hs.symm
      have h := Redispatch.counter_push_reverse rest []
      rw [hrest] at h
      have hpush : counterPush rest [] = [true, false, false, false, true, true] := by simpa using h
      rw [hpush] at hp
      simp only [List.cons.injEq, true_and] at hp
      exact ⟨rfl, rfl, hp.1.symm, hp.2.symm⟩

/-- The same actual blank execution performs two consecutive named zero
branches and returns to the grammar root after each one. -/
theorem second_zero_control_from_blank :
    ∃ (time1 time2 : Nat) (endHead : Int), 0 < time1 ∧ 0 < time2 ∧
      Related ⟨78, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ []),
          [false, false, true, true] ++ (List.replicate 3817 false ++ true :: false ::
            (bank (UnaryNine.values zeros ++ reserve) ++ [false]))⟩⟩
        ((machineWordSystem machine machineLabels).run (89821408 + time1 + time2)) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + time1 + time2) = [] := by
  obtain ⟨time1, head1, ht1, hr1, hout1⟩ := first_zero_control_raw
  have hr1' : Related ⟨79, head1,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: []),
        word2 ++ false :: false :: (List.replicate 3814 false ++ true :: false ::
          Redispatch.selectedPayload zeros r2 reserve [])⟩⟩
      ((machineWordSystem raw rawLabels).run (89821408 + time1)) := by
    have hl : List.replicate 6 false ++ false :: [] = List.replicate 7 false ++ [] := by decide
    rw [second_right, hl]
    exact hr1
  obtain ⟨runs, rest, time2, endHead, scratch1, scratch2, bit, pcTail, finish,
    hword, hsplit, hprefix, ht2, hp, hr, hq, hd, hout⟩ :=
    DecrementRoot.physical_root_zero_detail zeros r2 (by rfl) reserve 3814 word2 false path2 head1 [] []
      ((machineWordSystem raw rawLabels).run (89821408 + time1)) hr1'
  have hw : counterWord runs = [false, false, true, false, false, false, true, true] := by
    simpa [word2] using hword
  obtain ⟨hs1, hs2, hbit, hpc⟩ := split_word2 runs rest scratch1 scratch2 bit pcTail hw hsplit hprefix
  subst scratch1
  subst scratch2
  subst bit
  subst pcTail
  have hstart : mapConfig ((machineWordSystem raw rawLabels).run (89821408 + time1)) =
      (machineWordSystem machine machineLabels).run (89821408 + time1) := by
    rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  have hend : (machineWordSystem machine machineLabels).run (89821408 + time1 + time2) = mapConfig finish := by
    rw [WordEventSystem.run_add, ← hstart]
    exact hq.endpoint
  have houtput : (machineWordSystem machine machineLabels).prefixWord (89821408 + time1 + time2) = [] := by
    rw [WordEventSystem.prefix_add, ← prefix_eq, hout1, ← hstart, hq.output]
    rfl
  have hrel := FastBootstrap.Certificate.related_map hr
  have hqstate : mapState 79 = 78 := by decide
  change Related ⟨mapState 79, endHead, _⟩ _ at hrel
  rw [hqstate] at hrel
  refine ⟨time1, time2, endHead, ht1, ht2, ?_, houtput⟩
  rw [hend]
  simpa using hrel
end PASoundness.M236.BlankFirst
