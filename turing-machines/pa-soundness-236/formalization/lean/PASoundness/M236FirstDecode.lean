import PASoundness.M236UnifiedDecrement
import PASoundness.M236RuntimeGeometry
import PASoundness.M236BlankFirst
/-! The exact residual control word after the first blank-start zero branch. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.BlankFirst
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- A four-zero path has this unique pair of scratch lengths and control tail. -/
theorem split_word (runs rest : List (Fin 6)) (scratch1 scratch2 : Nat) (bit : Bool) (pcTail : List Bool)
    (hw : counterWord runs = [false, false, false, false, false, true, true])
    (hs : counterWord runs = List.replicate scratch1 true ++ false ::
      (List.replicate scratch2 true ++ false :: counterWord rest))
    (hp : counterPush rest [] = true :: bit :: pcTail) :
    scratch1 = 0 ∧ scratch2 = 0 ∧ bit = false ∧ pcTail = [false, false, true] := by
  rw [hw] at hs
  cases scratch1 with
  | succ n => simp [List.replicate_succ] at hs
  | zero =>
    cases scratch2 with
    | succ n => simp [List.replicate_succ] at hs
    | zero =>
      have hrest : counterWord rest = [false, false, false, true, true] := by simpa using hs.symm
      have h := Redispatch.counter_push_reverse rest []
      rw [hrest] at h
      have hpush : counterPush rest [] = [true, false, false, false, true] := by simpa using h
      rw [hpush] at hp
      simp only [List.cons.injEq, true_and] at hp
      exact ⟨rfl, rfl, hp.1.symm, hp.2.symm⟩
/-- The first blank-start decrement has a uniquely determined residual control
word and zero padding. Its finite duration and head position are existential. -/
theorem first_zero_control_from_blank :
    ∃ (time : Nat) (endHead : Int), 0 < time ∧
      Related ⟨78, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ []),
          [false, false, true] ++ (List.replicate 3818 false ++ true :: false ::
            (bank (UnaryNine.values zeros ++ reserve) ++ [false]))⟩⟩
        ((machineWordSystem machine machineLabels).run (89821408 + time)) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + time) = [] := by
  obtain ⟨runs, rest, time, endHead, scratch1, scratch2, bit, pcTail, finish,
    hword, hsplit, hprefix, ht, hp, hr, hq, hd, hout⟩ :=
    DecrementRoot.physical_root_zero_detail zeros r (by rfl) reserve 3815 word false path (-3818) [] []
      ((machineWordSystem raw rawLabels).run 89821408) root_related
  have hw : counterWord runs = [false, false, false, false, false, true, true] := by
    simpa [word] using hword
  obtain ⟨hs1, hs2, hbit, hpc⟩ := split_word runs rest scratch1 scratch2 bit pcTail hw hsplit hprefix
  subst scratch1
  subst scratch2
  subst bit
  subst pcTail
  have hstart : mapConfig ((machineWordSystem raw rawLabels).run 89821408) =
      (machineWordSystem machine machineLabels).run 89821408 := by
    rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  have hend : (machineWordSystem machine machineLabels).run (89821408 + time) = mapConfig finish := by
    rw [WordEventSystem.run_add, ← hstart]
    exact hq.endpoint
  have houtput : (machineWordSystem machine machineLabels).prefixWord (89821408 + time) = [] := by
    rw [WordEventSystem.prefix_add, RuntimeGeometry.selected_entry_geometry.2, ← hstart, hq.output]
    rfl
  have hrel := FastBootstrap.Certificate.related_map hr
  have hqstate : mapState 79 = 78 := by decide
  change Related ⟨mapState 79, endHead, _⟩ _ at hrel
  rw [hqstate] at hrel
  refine ⟨time, endHead, ht, ?_, houtput⟩
  rw [hend]
  simpa using hrel
end PASoundness.M236.BlankFirst
