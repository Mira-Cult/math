import Shared.Beeping.NPcoNP.NativeAllZeroSelector
import Shared.Beeping.NPcoNP.Bootstrap284NextSelector
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue

/-! The actual blank-start all-zero selector takes the state-261 branch
and completes its exact fill-and-return segment. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeAllZeroSelector
open Shared.Beeping.NPcoNP.Bootstrap284NextSelector
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.Bootstrap284ManyCarry
open Shared.Beeping.NPcoNP.Bootstrap284ManyShift
open Shared.Beeping.NPcoNP.Bootstrap284TerminalUnit
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284Unit261Seed
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 9000000

def afterAllZero : Int → Bool := fillRange (setAt (-4) nextTape) (-2) 3

theorem nextTape_low_zero : ∀ q : Int, -6<q → q<1 → nextTape q=false := by
  intro q hq hq'
  have hz := scan28_cells.2.1 q hq hq'
  simpa [nextTape,put,clearRange,show q≠3 by omega,show ¬(1≤q ∧ q<4) by omega] using hz

theorem nextTape_scan_cells : nextTape (-5)=false ∧ nextTape (-4)=false ∧
    nextTape (-3)=false ∧ (∀ i : Nat, i<5 → nextTape (-2+(i : Int))=false) ∧
    nextTape 3=true := by
  refine ⟨nextTape_low_zero (-5) (by omega) (by omega),
    nextTape_low_zero (-4) (by omega) (by omega),
    nextTape_low_zero (-3) (by omega) (by omega),?_,?_⟩
  · intro i hi
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact nextTape_low_zero _ (by omega) (by omega) | simp [nextTape,put,clearRange]
  · simp [nextTape,put]

/-- The literal selector and following fill return to state 83 in exactly
39 silent transitions, with the complete output tape specified. -/
theorem all_zero_return :
    silentSegment machine (cfg 93 (-34) nextTape) (cfg 83 1 afterAllZero) 39 := by
  have hw : Holds nextTape (-34) (markerWindow (List.replicate 13 0 ++ [0])) := by
    simpa using nextTape_window.2.2
  obtain ⟨h5,h4,h3,hzeros,hone⟩ := nextTape_scan_cells
  have h := all_zero_fill_return nextTape (-34) 13 5 (by decide) hw
    (by simpa using nextTape_window.1) (by simpa using h5)
    (by simpa using h4) (by simpa using h3)
    (by simpa using hzeros) (by simpa using hone)
  simpa [afterAllZero] using h

/-- Blank-start reachability of the next return; the earlier initialization
segment's duration remains existential. -/
theorem blank_start_all_zero_return : ∃ m : Nat, 0<m ∧
    silentSegment machine (machine.system.run 0) (cfg 83 1 afterAllZero)
      (2133669+m+67+76+10+20+29+39) := by
  obtain ⟨m,hm,hstart⟩ := blank_start_next_selector93_exact
  exact ⟨m,hm,segAdd machine _ _ _ (2133669+m+67+76+10+20+29) 39 hstart all_zero_return⟩

/-- The returned tape has the next concrete fourteen-block window. -/
theorem afterAllZero_window :
    Holds afterAllZero (-30) (markerWindow (List.replicate 11 0 ++ [1,0,3])) ∧
    afterAllZero (-31)=true ∧ afterAllZero 2=true := by
  have he : markerWindow (List.replicate 11 0 ++ [1,0,3]) = [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,false,true,false,true,true,true,true] := by decide
  rw [he]
  unfold afterAllZero nextTape scanTape carryTape shiftedTape afterDispatch
  rw [postReturn_eq]
  unfold returnedTape currentTape
  rw [run_2133586]
  simp only [Holds]
  all_goals decide

/-- The next selector takes its unit dispatch and finishes the following
zero-length state-16 scan in 61 silent transitions. -/
theorem all_zero_to_next_unit :
    silentSegment machine (cfg 83 1 afterAllZero)
      (cfg 12 (-2) (NativeHalfState16Progress.clearAt (-4) afterAllZero)) 61 := by
  have hw : Holds afterAllZero (-30) (markerWindow (List.replicate 11 0 ++ 1::0::3::[])) := by
    simpa using afterAllZero_window.1
  have hs := marker_window_to93 afterAllZero (-30) (List.replicate 11 0 ++ [1,0,3])
    (by decide) (by simpa using hw) afterAllZero_window.2.1
  have hs' : silentSegment machine (cfg 83 1 afterAllZero) (cfg 93 (-30) afterAllZero) 33 := by
    simpa [UnaryBank.encode,UnaryBank.block,List.replicate_succ] using hs
  have hd := marker_unit_to12 afterAllZero (-30) 11 0 3 [] hw
  have hd' : silentSegment machine (cfg 93 (-30) afterAllZero)
      (cfg 12 (-2) (NativeHalfState16Progress.clearAt (-4) afterAllZero)) 28 := by
    simpa using hd
  exact segAdd machine _ _ _ 33 28 hs' hd'

/-- Compose both exact local segments with the checked blank-start seed. -/
theorem blank_start_next_unit : ∃ m : Nat, 0<m ∧
    silentSegment machine (machine.system.run 0)
      (cfg 12 (-2) (NativeHalfState16Progress.clearAt (-4) afterAllZero))
      (2133669+m+67+76+10+20+29+39+61) := by
  obtain ⟨m,hm,hstart⟩ := blank_start_all_zero_return
  exact ⟨m,hm,segAdd machine _ _ _ (2133669+m+67+76+10+20+29+39) 61
    hstart all_zero_to_next_unit⟩

#print axioms blank_start_next_unit
#print axioms afterAllZero_window
#print axioms all_zero_to_next_unit
#print axioms nextTape_scan_cells
#print axioms all_zero_return
#print axioms blank_start_all_zero_return
end Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn
