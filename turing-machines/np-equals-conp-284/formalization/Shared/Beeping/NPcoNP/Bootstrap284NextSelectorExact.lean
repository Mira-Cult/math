import Shared.Beeping.NPcoNP.Bootstrap284NextReturnExact
import Shared.Beeping.NPcoNP.Bootstrap284NextSelector

/-! Recover the marked selector after the exact positive-bank return. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284NextSelectorExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.Bootstrap284NextReturnExact
open Shared.Beeping.NPcoNP.Bootstrap284NextBankExact
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284TerminalFullExact
open Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn
open Shared.Beeping.NPcoNP.Bootstrap284ManyCarry
open Shared.Beeping.NPcoNP.Bootstrap284ManyShift
open Shared.Beeping.NPcoNP.Bootstrap284TerminalUnit
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- The later return preserves the physical tape strictly left of its
new marker. -/
theorem return_left (q : Int) (hq : q< -8) : returnTape q=nextBankTape q := by
  simp [returnTape,scanTape,carryTape,result,cleared,put,clearRange,
    show q≠3 by omega,show ¬((-1:Int)≤q ∧ q<4) by omega,
    show q≠ -2 by omega,show q≠ -8 by omega,
    show ¬((-8:Int)<q ∧ q≤ -5) by omega]

/-- The earlier initialization operations also preserve that part of the
tape, so it can be read from the checked bootstrap snapshot. -/
theorem terminal_left (q : Int) (hq : q< -8) : terminalTape q=postReturn q := by
  simp [terminalTape,afterAllZero,fillRange,setAt,
    Bootstrap284NextSelector.nextTape,clearRange,Bootstrap284NextSelector.scanTape,
    Bootstrap284NextSelector.carryTape,result,cleared,put,shiftedTape,afterDispatch,clearAt,
    show q≠ -5 by omega,show q≠5 by omega,show q≠6 by omega,show q≠7 by omega,
    show q≠8 by omega,show ¬((-2:Int)≤q ∧ q<3) by omega,show q≠ -4 by omega,
    show q≠3 by omega,show ¬((1:Int)≤q ∧ q<4) by omega,show q≠0 by omega,
    show q≠ -6 by omega,show ¬((-6:Int)<q ∧ q≤ -3) by omega,show q≠ -2 by omega]

theorem return_left_source (q : Int) (hq : q< -8) : returnTape q=postReturn q := by
  rw [return_left q hq, next_bank_segment.2.1 q (by omega) (by omega),terminal_left q hq]

theorem source_window :
    Holds postReturn (-36) (markerWindow (List.replicate 14 0)) ∧ postReturn (-37)=true := by
  have he : markerWindow (List.replicate 14 0) =
      [false,true,false,true,false,true,false,true,false,true,false,true,false,true,
       false,true,false,true,false,true,false,true,false,true,false,true,false,true] := by decide
  rw [he,postReturn_eq]
  unfold returnedTape currentTape
  rw [run_2133586]
  simp only [Holds]
  all_goals decide

/-- The new selector has fourteen paid zero blocks and its two boundary
markers at their exact physical coordinates. -/
theorem return_window :
    Holds returnTape (-36) (markerWindow (List.replicate 14 0)) ∧
      returnTape (-37)=true ∧ returnTape (-8)=true := by
  refine ⟨?_,?_,?_⟩
  · apply holds_transport postReturn returnTape (-36) _ source_window.1
    intro q _ hq
    have hl : (markerWindow (List.replicate 14 0)).length=28 := by
      rw [markerWindow_length,zeros_length]
    rw [hl] at hq
    exact (return_left_source q (by omega)).symm
  · rw [return_left_source (-37) (by omega)]
    exact source_window.2
  · simp [returnTape,put,clearRange,scan28_cells.1]

/-- The literal blank-start run reaches the next state-93 selector exactly
29 transitions later, with its full tape unchanged. -/
theorem blank_start_next_selector_exact :
    machine.system.run 2134248=cfg 93 (-36) returnTape ∧
    Holds returnTape (-36) (markerWindow (List.replicate 14 0)) ∧
    returnTape (-37)=true ∧ returnTape (-8)=true ∧
    silentSegment machine (machine.system.run 0) (cfg 93 (-36) returnTape) 2134248 := by
  have hs := marker_window_to93 returnTape (-36) (List.replicate 14 0)
    (by decide) return_window.1 return_window.2.1
  have hs' : silentSegment machine (cfg 83 (-9) returnTape) (cfg 93 (-36) returnTape) 29 := by
    simpa [encode,block,List.replicate_succ] using hs
  have hall := segAdd machine _ _ _ 2134219 29 blank_start_next_return_exact.2 hs'
  exact ⟨run_of_initial_segment 2134248 _ hall,return_window.1,return_window.2.1,
    return_window.2.2,hall⟩

#print axioms blank_start_next_selector_exact
end Shared.Beeping.NPcoNP.Bootstrap284NextSelectorExact
