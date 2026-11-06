import Shared.Beeping.NPcoNP.NativeUnit261Return1
import Shared.Beeping.NPcoNP.Bootstrap284Unit261Seed

/-! The parameterized return applies at the verified blank-start seed. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284Unit261Return
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeUnit261Return1
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
open Shared.Beeping.NPcoNP.Bootstrap284ThirdIncrement
open Shared.Beeping.NPcoNP.Bootstrap284Unit261Seed
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- The actual return after the selected increment reaches state 1 at -3
with exactly the already-certified post-increment tape, silently. -/
theorem blank_start_unit_return1 :
    silentSegment machine (machine.system.run 0)
      (cfg 1 (-3) (setAt 6 (clearAt (-2) returnedTape))) 2133669 := by
  obtain ⟨mid,_hstate,_hbank,_hmark,_hframe,hfirst,hreturn⟩ :=
    dispatch_increment_return1 4 0 [] (-2) returnedTape (by decide)
      actual_q261_one actual_q261_next_zero actual_scanword actual_bank
  have hs : silentSegment machine (machine.system.run 2133650) mid 10 := by
    rw [run_2133650]
    simpa [encode] using hfirst
  have he : machine.system.run (2133650+10)=mid := by
    rw [EventSystem.run_add,← ScalarWordRefinement.advance_ofBeep]
    exact hs.1
  have he' : mid=cfg 23 6 (setAt 6 (clearAt (-2) returnedTape)) := by
    have he'' : machine.system.run 2133660=mid := by
      simpa only [show 2133650+10=2133660 by decide] using he
    exact he''.symm.trans run_2133660
  rw [he'] at hreturn
  have hreturn' : silentSegment machine
      (cfg 23 6 (setAt 6 (clearAt (-2) returnedTape)))
      (cfg 1 (-3) (setAt 6 (clearAt (-2) returnedTape))) 9 := by
    simpa [cfg,encode,block] using hreturn
  have h := segAdd machine _ _ _ 2133660 9 blank_start_third_increment_exact hreturn'
  simpa using h

#print axioms blank_start_unit_return1
end Shared.Beeping.NPcoNP.Bootstrap284Unit261Return
