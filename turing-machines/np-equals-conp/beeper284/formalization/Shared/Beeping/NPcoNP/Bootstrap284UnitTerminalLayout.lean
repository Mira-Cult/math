import Shared.Beeping.NPcoNP.NativeUnitTerminalLayout
import Shared.Beeping.NPcoNP.Bootstrap284UnitNext93
import Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalNet

/-! Recover the next marked window and protected bank sentinel after the
concrete compound unit/terminal segment. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalLayout
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeUnitTerminalLayout
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284NextSelector
open Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn
open Shared.Beeping.NPcoNP.Bootstrap284UnitWindow83
open Shared.Beeping.NPcoNP.Bootstrap284UnitNext93
open Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalNet
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

theorem after_extra_blank : afterAllZero 10=false := by
  rw [after_bank_frame 10 (by decide)]
  unfold shiftedTape afterDispatch
  rw [postReturn_eq]
  unfold returnedTape currentTape
  rw [run_2133586]
  decide

theorem after_bank_two_blanks : Holds afterAllZero 5 (encode [0,0] ++ [false,false]) := by
  have ht : Holds afterAllZero (5+((encode [0,0] ++ [false]).length : Int)) [false] := by
    simpa [encode,block,Holds] using after_extra_blank
  have h := holds_append_intro afterAllZero 5 (encode [0,0] ++ [false]) [false] after_bank ht
  simpa [List.append_assoc] using h

theorem after_control_left : afterAllZero (-32)=false ∧ afterAllZero (-31)=true ∧
    afterAllZero (-33)=true := by
  let xs := markerWindow (List.replicate 13 0 ++ [1])
  have hl : xs.length=29 := by decide
  have h1 := holds_get afterAllZero (-34) xs after_next_window.1 1 (by omega)
  have h2 := holds_get afterAllZero (-34) xs after_next_window.1 2 (by omega)
  have hv1 : xs[1]=true := by decide
  have hv2 : xs[2]=false := by decide
  rw [hv1] at h1
  rw [hv2] at h2
  exact ⟨by simpa using h2,afterAllZero_window.2.1,by simpa using h1⟩

/-- The finite compound segment reaches a new fourteen-block control window,
with both markers and an incremented bank retaining its trailing blank. -/
theorem checked_next_layout : ∃ (mid : Config 284) (n : Nat), mid.state=23 ∧ 0<n ∧
    Holds (terminalOut mid) (-32) (markerWindow (List.replicate 12 0 ++ [3,3])) ∧
    terminalOut mid (-33)=true ∧ terminalOut mid 2=true ∧
    Holds (terminalOut mid) 5 (encode [1,0] ++ [false]) ∧
    silentSegment machine (cfg 83 1 afterAllZero) (cfg 83 1 (terminalOut mid)) (155+n) := by
  have hw : Holds afterAllZero (-30) (markerWindow (List.replicate 11 0 ++ 1::0::3::[])) := by
    simpa using afterAllZero_window.1
  have hentry := marker_window_to93 afterAllZero (-30) (List.replicate 11 0 ++ [1,0,3])
    (by decide) (by simpa using hw) afterAllZero_window.2.1
  have hentry' : silentSegment machine (cfg 83 1 afterAllZero) (cfg 93 (-30) afterAllZero) 33 := by
    simpa [encode,block,List.replicate_succ] using hentry
  obtain ⟨mid,n,hs,hn,_hlen,hnext,hbefore,hmark,hbank,_hext,_hframe,_hhead,hseg⟩ :=
    unit_terminal_next_layout afterAllZero (-30) (-34) 11 3 6 0 [] [0] hw (by decide) (by decide)
      (by simpa using after_pre) (by simpa using after_scanword) (by simpa using after_bank_two_blanks)
      (by decide) after_next_window.1 after_next_window.2
      (by simpa using after_control_left.1) (by simpa using after_control_left.2.1)
      (by simpa using after_control_left.2.2) (by simpa [encode,block,List.replicate_succ] using afterAllZero_window.2.2)
      (by decide)
  have hw' : Holds (terminalOut mid) (-32) (markerWindow (List.replicate 12 0 ++ [3,3])) := by
    simpa [terminalOut] using hnext
  have hb : Holds (terminalOut mid) 5 (encode [1,0] ++ [false]) := by simpa [terminalOut,encode,block] using hbank
  have hc : silentSegment machine (cfg 93 (-30) afterAllZero) (cfg 83 1 (terminalOut mid)) (122+n) := by
    have hh : silentSegment machine (cfg 93 (-30) afterAllZero)
        (cfg 83 1 (terminalOut mid)) (40+(13+n+69)) := by
      simpa [terminalOut,encode,block] using hseg
    have he : 40+(13+n+69)=122+n := by omega
    rw [he] at hh
    exact hh
  have hall := segAdd machine _ _ _ 33 (122+n) hentry' hc
  have hcost : 33+(122+n)=155+n := by omega
  rw [hcost] at hall
  exact ⟨mid,n,hs,hn,hw',by simpa [terminalOut] using hbefore,
    by simpa [terminalOut,encode,block,List.replicate_succ] using hmark,hb,hall⟩

/-- The new selector layout occurs on a blank-start execution. -/
theorem blank_start_next_layout : ∃ (m n : Nat) (mid : Config 284), 0<m ∧ 0<n ∧ mid.state=23 ∧
    Holds (terminalOut mid) (-32) (markerWindow (List.replicate 12 0 ++ [3,3])) ∧
    terminalOut mid (-33)=true ∧ terminalOut mid 2=true ∧
    Holds (terminalOut mid) 5 (encode [1,0] ++ [false]) ∧
    silentSegment machine (machine.system.run 0) (cfg 83 1 (terminalOut mid))
      (2133669+m+67+76+10+20+29+39+(155+n)) := by
  obtain ⟨m,hm,hstart⟩ := blank_start_all_zero_return
  obtain ⟨mid,n,hs,hn,hw,hbefore,hmark,hbank,hseg⟩ := checked_next_layout
  exact ⟨m,n,mid,hm,hn,hs,hw,hbefore,hmark,hbank,
    segAdd machine _ _ _ (2133669+m+67+76+10+20+29+39) (155+n) hstart hseg⟩

#print axioms after_bank_two_blanks
#print axioms checked_next_layout
#print axioms blank_start_next_layout
end Shared.Beeping.NPcoNP.Bootstrap284UnitTerminalLayout
