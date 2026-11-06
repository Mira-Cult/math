import Shared.Beeping.NPcoNP.NativeUnitWindowIncrement83
import Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn
import Shared.Beeping.NPcoNP.Bootstrap284ManyTerminalActual

/-! Instantiate the unit-window increment return on the checked blank-start
seed after the all-zero selector. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284UnitWindow83
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
open Shared.Beeping.NPcoNP.NativeIncBlock
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeUnitWindowIncrement83
open Shared.Beeping.NPcoNP.Bootstrap284NextSelector
open Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn
open Shared.Beeping.NPcoNP.Bootstrap284ManyCarry
open Shared.Beeping.NPcoNP.Bootstrap284ManyShift
open Shared.Beeping.NPcoNP.Bootstrap284ManyTerminalActual
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 12000000

theorem after_bank_frame : ∀ q : Int, 5≤q → afterAllZero q=shiftedTape q := by
  intro q hq
  simp [afterAllZero,fillRange,setAt,nextTape,put,clearRange,scanTape,carryTape,result,cleared,
    show ¬((-2:Int)≤q ∧ q<3) by omega,show q≠ -4 by omega,show q≠3 by omega,
    show ¬((1:Int)≤q ∧ q<4) by omega,show q≠0 by omega,show q≠ -6 by omega,
    show ¬((-6:Int)<q ∧ q≤ -3) by omega]

theorem after_bank : Holds afterAllZero 5 (encode [0,0] ++ [false]) := by
  have hs : Holds shiftedTape 5 (encode [0,0] ++ [false]) := by
    simpa [shiftedTape,afterDispatch] using checked_terminal_many.1
  apply holds_transport shiftedTape afterAllZero 5 _ hs
  intro q hq _
  symm
  exact after_bank_frame q hq

theorem after_scanword : Holds afterAllZero (-2) (List.replicate 6 true ++ [false]) := by
  apply holds_ones_delimiter 6 (-2) afterAllZero
  · intro i hi
    by_cases hsmall : i<5
    · have hp : (-2:Int)≤ -2+(i : Int) ∧ -2+(i : Int)<3 := by omega
      simp [afterAllZero,fillRange,hp]
    · have hi5 : i=5 := by omega
      subst i
      have ht : nextTape 3=true := nextTape_scan_cells.2.2.2.2
      simpa [afterAllZero,fillRange,setAt] using ht
  · have hz : nextTape 4=false := by
      simpa [nextTape,put,clearRange] using scan28_cells.2.2
    simpa [afterAllZero,fillRange,setAt] using hz

theorem after_pre : afterAllZero (-5)=false := by
  have hz := nextTape_low_zero (-5) (by omega) (by omega)
  simpa [afterAllZero,fillRange,setAt] using hz

def cycleOut (mid : Config 284) : Int → Bool :=
  put (clearRange (put (put mid.tape (-5) true) (-2) false) (-1) 4) 3 true

/-- The recovered unit window selects and increments the first bank value,
then returns to state 83. The final tape expression and local duration are explicit. -/
theorem unit_window_cycle : ∃ mid : Config 284, mid.state=23 ∧
    Holds (cycleOut mid) 5 (encode [1,0]) ∧
    silentSegment machine (cfg 83 1 afterAllZero) (cfg 83 (-6) (cycleOut mid)) 105 := by
  have hw : Holds afterAllZero (-30) (markerWindow (List.replicate 11 0 ++ 1::0::3::[])) := by
    simpa using afterAllZero_window.1
  have hentry := marker_window_to93 afterAllZero (-30) (List.replicate 11 0 ++ [1,0,3])
    (by decide) (by simpa using hw) afterAllZero_window.2.1
  have hentry' : silentSegment machine (cfg 83 1 afterAllZero) (cfg 93 (-30) afterAllZero) 33 := by
    simpa [encode,block,List.replicate_succ] using hentry
  obtain ⟨mid,hs,hmid,hfirst,hout,_hframe,_hmarker,_hleft,hreturn⟩ :=
    unit_window_increment_to83_exact afterAllZero (-30) 11 3 6 0 [] [0] hw (by decide)
      (by simpa using after_pre) (by simpa using after_scanword) (by simpa using after_bank)
  have hfirst' : silentSegment machine (cfg 93 (-30) afterAllZero) mid 40 := by simpa [encode,block] using hfirst
  have hreturn' : silentSegment machine mid (cfg 83 (-6) (cycleOut mid)) 32 := by
    simpa [cycleOut,encode,block] using hreturn
  have hbank : Holds (cycleOut mid) 5 (encode [1,0]) := by simpa [cycleOut,encode,block] using hout
  have hpre := segAdd machine _ _ _ 33 40 hentry' hfirst'
  have hall := segAdd machine _ _ _ (33+40) 32 hpre hreturn'
  exact ⟨mid,hs,hbank,hall⟩

/-- The unit increment cycle occurs after the certified blank-start prefix. -/
theorem blank_start_unit_window_cycle : ∃ (m : Nat) (mid : Config 284), 0<m ∧
    mid.state=23 ∧ Holds (cycleOut mid) 5 (encode [1,0]) ∧
    silentSegment machine (machine.system.run 0) (cfg 83 (-6) (cycleOut mid))
      (2133669+m+67+76+10+20+29+39+105) := by
  obtain ⟨m,hm,hstart⟩ := blank_start_all_zero_return
  obtain ⟨mid,hs,hbank,hcycle⟩ := unit_window_cycle
  exact ⟨m,mid,hm,hs,hbank,
    segAdd machine _ _ _ (2133669+m+67+76+10+20+29+39) 105 hstart hcycle⟩

#print axioms after_bank_frame
#print axioms after_scanword
#print axioms unit_window_cycle
#print axioms blank_start_unit_window_cycle
end Shared.Beeping.NPcoNP.Bootstrap284UnitWindow83
