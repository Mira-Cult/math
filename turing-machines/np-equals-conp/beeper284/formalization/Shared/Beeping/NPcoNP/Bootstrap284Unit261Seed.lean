import Shared.Beeping.NPcoNP.NativeUnit261Increment
import Shared.Beeping.NPcoNP.Bootstrap284ThirdIncrement

/-! The generalized unit-dispatch increment applies to a checked blank-start
configuration. It is a finite seed, not a recurrent graph invariant. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284Unit261Seed
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeUnit261Increment
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
open Shared.Beeping.NPcoNP.Bootstrap284ThirdIncrement
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

theorem actual_window_shape : Holds returnedTape (-28)
    (markerWindow (List.replicate 11 0 ++ 1::0::1::[])) := by
  simpa [selector] using actual_window

theorem actual_q261_segment : silentSegment machine (cfg 93 (-28) returnedTape)
    (cfg 261 (-2) returnedTape) 26 := by
  have h := marker_window_to_one returnedTape (-28) 11 [0,1] (by decide) actual_window_shape
  simpa using h

theorem run_2133650 : machine.system.run 2133650=cfg 261 (-2) returnedTape := by
  apply run_of_initial_segment 2133650 _
  have h := segAdd machine _ _ _ 2133624 26 blank_start_timed_return actual_q261_segment
  simpa using h

theorem actual_q261_one : returnedTape (-2)=true := by
  have h := one_marker_tail returnedTape (-28) 11 0 1 [] actual_window_shape
  simpa using h.1

theorem actual_q261_next_zero : returnedTape (-1)=false := by
  have h := one_marker_tail returnedTape (-28) 11 0 1 [] actual_window_shape
  have hz := h.2.1
  simpa using hz

theorem actual_scanword : Holds returnedTape 0 (List.replicate 4 true ++ [false]) := by
  unfold returnedTape currentTape
  rw [run_2133586]
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds]
  all_goals decide

theorem actual_bank : Holds returnedTape 5 (encode [0] ++ [false]) := by
  apply holds_transport (clearAt (-2) returnedTape) returnedTape 5 _ actual_increment_bank
  intro p hp _
  simp [clearAt,show p≠(-2) by omega]

/-- The same parameterized macro applies at the actual state-261 visit. -/
theorem actual_dispatch_increment :
    silentSegment machine (machine.system.run 2133650)
      (cfg 23 6 (setAt 6 (clearAt (-2) returnedTape))) 10 := by
  obtain ⟨e,_hstate,_hhead,_hbank,_hmarker,_hframe,hseg⟩ :=
    dispatch_increment 4 0 [] (-2) returnedTape actual_q261_one actual_q261_next_zero
      actual_scanword actual_bank
  have hseg' : silentSegment machine (machine.system.run 2133650) e 10 := by
    rw [run_2133650]
    simpa [encode] using hseg
  have he : machine.system.run (2133650+10)=e := by
    rw [EventSystem.run_add,← ScalarWordRefinement.advance_ofBeep]
    exact hseg'.1
  have he' : e=cfg 23 6 (setAt 6 (clearAt (-2) returnedTape)) := by
    have hr := run_2133660
    have he'' : machine.system.run 2133660=e := by
      simpa only [show 2133650+10=2133660 by decide] using he
    exact he''.symm.trans hr
  rwa [he'] at hseg'

#print axioms run_2133650
#print axioms actual_dispatch_increment
end Shared.Beeping.NPcoNP.Bootstrap284Unit261Seed
