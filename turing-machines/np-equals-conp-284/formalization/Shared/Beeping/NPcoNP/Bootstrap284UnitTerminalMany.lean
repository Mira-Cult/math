import Shared.Beeping.NPcoNP.NativeUnitTerminalMany
import Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalLayout

/-! The checked seed composes the unit/terminal cycle with the next many
selector and reaches its state-23 bank update. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalMany
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeUnitTerminalMany
open Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalLayout
open Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalNet
open Shared.Beeping.NPcoNP.Bootstrap284UnitNext93
open Shared.Beeping.NPcoNP.Bootstrap284UnitWindow83
open Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn
open Shared.Beeping.NPcoNP.Bootstrap284ManyCarry
open Shared.Beeping.NPcoNP.Bootstrap284ManyShift
open Shared.Beeping.NPcoNP.Bootstrap284TerminalUnit
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284Unit261Seed
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

theorem after_third_blank : afterAllZero 11=false := by
  rw [after_bank_frame 11 (by decide)]
  unfold shiftedTape afterDispatch
  rw [postReturn_eq]
  unfold returnedTape currentTape
  rw [run_2133586]
  decide

theorem after_bank_three_blanks : Holds afterAllZero 5 (encode [0,0] ++ [false,false,false]) := by
  have ht : Holds afterAllZero (5+((encode [0,0] ++ [false,false]).length : Int)) [false] := by
    simpa [encode,block,Holds] using after_third_blank
  have h := holds_append_intro afterAllZero 5 (encode [0,0] ++ [false,false]) [false] after_bank_two_blanks ht
  simpa [List.append_assoc] using h

def manyOut (mid : Config 284) : Int → Bool := spec (clearAt (-4) (terminalOut mid)) 9 4

/-- Following the unit/terminal cycle, the next terminal-many selector
performs its bank shift and reaches state 23 with the resulting encoded word. -/
theorem checked_unit_then_many : ∃ (mid : Config 284) (n : Nat), mid.state=23 ∧ 0<n ∧
    Holds (manyOut mid) 5 (encode [0,0] ++ [true,false,false]) ∧
    silentSegment machine (cfg 83 1 afterAllZero) (cfg 23 3 (manyOut mid)) (239+n) := by
  have hw : Holds afterAllZero (-30) (markerWindow (List.replicate 11 0 ++ [1,0,3])) := afterAllZero_window.1
  have hentry := marker_window_to93 afterAllZero (-30) (List.replicate 11 0 ++ [1,0,3])
    (by decide) hw afterAllZero_window.2.1
  have hentry' : silentSegment machine (cfg 83 1 afterAllZero) (cfg 93 (-30) afterAllZero) 33 := by
    simpa [encode,block,List.replicate_succ] using hentry
  obtain ⟨mid,n,hs,hn,_hw,_hbank,hout,hseg⟩ :=
    unit_terminal_to_many afterAllZero (-30) (-34) 11 3 6 0 [0] hw (by decide) (by decide)
      (by simpa using after_pre) (by simpa using after_scanword) (by simpa using after_bank_three_blanks)
      (by decide) after_next_window.1 after_next_window.2
      (by simpa using after_control_left.1) (by simpa using after_control_left.2.1)
      (by simpa using after_control_left.2.2)
      (by simpa [encode,block,List.replicate_succ] using afterAllZero_window.2.2) (by decide)
  have hout' : Holds (manyOut mid) 5 (encode [0,0] ++ [true,false,false]) := by
    simpa [manyOut,terminalOut,encode,block] using hout
  have hseg' : silentSegment machine (cfg 93 (-30) afterAllZero) (cfg 23 3 (manyOut mid)) (206+n) := by
    have hh : silentSegment machine (cfg 93 (-30) afterAllZero) (cfg 23 3 (manyOut mid))
        (40+(13+n+69)+84) := by
      simpa [manyOut,terminalOut,encode,block,List.replicate_succ] using hseg
    have he : 40+(13+n+69)+84=206+n := by omega
    rw [he] at hh
    exact hh
  have hall := segAdd machine _ _ _ 33 (206+n) hentry' hseg'
  have hcost : 33+(206+n)=239+n := by omega
  rw [hcost] at hall
  exact ⟨mid,n,hs,hn,hout',hall⟩

/-- Blank-start reachability of the composed state-23 bank shift. -/
theorem blank_start_unit_then_many : ∃ (m n : Nat) (mid : Config 284), 0<m ∧ 0<n ∧ mid.state=23 ∧
    Holds (manyOut mid) 5 (encode [0,0] ++ [true,false,false]) ∧
    silentSegment machine (machine.system.run 0) (cfg 23 3 (manyOut mid))
      (2133669+m+67+76+10+20+29+39+(239+n)) := by
  obtain ⟨m,hm,hstart⟩ := blank_start_all_zero_return
  obtain ⟨mid,n,hs,hn,hbank,hseg⟩ := checked_unit_then_many
  exact ⟨m,n,mid,hm,hn,hs,hbank,
    segAdd machine _ _ _ (2133669+m+67+76+10+20+29+39) (239+n) hstart hseg⟩

#print axioms after_bank_three_blanks
#print axioms checked_unit_then_many
#print axioms blank_start_unit_then_many
end Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalMany
