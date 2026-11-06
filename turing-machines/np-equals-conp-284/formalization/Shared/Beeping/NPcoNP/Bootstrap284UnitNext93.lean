import Shared.Beeping.NPcoNP.NativeUnitWindowNext93
import Shared.Beeping.NPcoNP.Bootstrap284UnitWindow83
import Shared.Beeping.NPcoNP.NativeTerminalUnitSelector

/-! The checked unit increment exposes its next selector window. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284UnitNext93
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeUnitWindowNext93
open Shared.Beeping.NPcoNP.Bootstrap284NextSelector
open Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn
open Shared.Beeping.NPcoNP.Bootstrap284UnitWindow83
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 12000000

theorem after_next_window :
    Holds afterAllZero (-34) (markerWindow (List.replicate 13 0 ++ [1])) ∧
    afterAllZero (-35)=true := by
  have he : markerWindow (List.replicate 13 0 ++ [1]) =
      markerWindow (List.replicate 14 0) ++ [true] := by decide
  have hw : Holds afterAllZero (-34) (markerWindow (List.replicate 14 0)) := by
    apply holds_transport nextTape afterAllZero (-34) _ nextTape_window.2.2
    intro q _ hq
    have hl : (markerWindow (List.replicate 14 0)).length=28 := by
      rw [markerWindow_length,zeros_length]
    rw [hl] at hq
    simp [afterAllZero,fillRange,setAt,show ¬((-2:Int)≤q ∧ q<3) by omega,
      show q≠ -4 by omega]
  have hm : afterAllZero (-6)=true := by
    simpa [afterAllZero,fillRange,setAt] using nextTape_window.1
  have hleft : afterAllZero (-35)=true := by
    simpa [afterAllZero,fillRange,setAt] using nextTape_window.2.1
  have ht : Holds afterAllZero (-34+((markerWindow (List.replicate 14 0)).length : Int)) [true] := by
    have hl : (markerWindow (List.replicate 14 0)).length=28 := by
      rw [markerWindow_length,zeros_length]
    rw [hl]
    change afterAllZero ((-34:Int)+28)=true ∧ True
    have hp : (-34:Int)+28= -6 := by omega
    rw [hp]
    exact ⟨hm,trivial⟩
  constructor
  · rw [he]
    exact holds_append_intro afterAllZero (-34) _ [true] hw ht
  · exact hleft

/-- The reachable unit increment and return expose, then read, a next
terminal unit window. The incremented bank remains present. -/
theorem unit_increment_reads_next : ∃ mid : Config 284, mid.state=23 ∧
    Holds (cycleOut mid) 5 (encode [1,0]) ∧
    Holds (cycleOut mid) (-34) (markerWindow (List.replicate 13 0 ++ [1])) ∧
    cycleOut mid (-35)=true ∧ cycleOut mid (-5)=true ∧
    silentSegment machine (cfg 83 1 afterAllZero) (cfg 93 (-34) (cycleOut mid)) 135 := by
  have hw : Holds afterAllZero (-30) (markerWindow (List.replicate 11 0 ++ 1::0::3::[])) := by
    simpa using afterAllZero_window.1
  have hentry := marker_window_to93 afterAllZero (-30) (List.replicate 11 0 ++ [1,0,3])
    (by decide) (by simpa using hw) afterAllZero_window.2.1
  have hentry' : silentSegment machine (cfg 83 1 afterAllZero) (cfg 93 (-30) afterAllZero) 33 := by
    simpa [encode,block,List.replicate_succ] using hentry
  have hpos : (-34:Int)+((encode (List.replicate 13 0 ++ [1])).length : Int)=
      (-30:Int)+((2*11 : Nat):Int)+3 := by
    have hl : (encode (List.replicate 13 0 ++ [1])).length=29 := by decide
    rw [hl]
    decide
  obtain ⟨mid,hs,hfirst,hbank,hnext,hbefore,hmark,_hprefix,hret⟩ :=
    unit_increment_next93 afterAllZero (-30) (-34) 11 3 6 0 [] [0]
      (List.replicate 13 0 ++ [1]) hw (by decide) (by simpa using after_pre)
      (by simpa using after_scanword) (by simpa using after_bank) (by decide)
      hpos after_next_window.1 after_next_window.2
  have hf : silentSegment machine (cfg 93 (-30) afterAllZero) mid 40 := by simpa [encode,block] using hfirst
  have hr : silentSegment machine mid (cfg 93 (-34) (cycleOut mid)) 62 := by
    simpa [cycleOut,encode,block,List.replicate_succ] using hret
  have hb : Holds (cycleOut mid) 5 (encode [1,0]) := by simpa [cycleOut,encode,block] using hbank
  have hn : Holds (cycleOut mid) (-34) (markerWindow (List.replicate 13 0 ++ [1])) := by
    simpa [cycleOut] using hnext
  have hc := segAdd machine _ _ _ 33 40 hentry' hf
  have hall := segAdd machine _ _ _ (33+40) 62 hc hr
  exact ⟨mid,hs,hb,hn,by simpa [cycleOut] using hbefore,
    by simpa [cycleOut] using hmark,hall⟩

/-- Compose with the certified blank-start prefix. -/
theorem blank_start_reads_next : ∃ (m : Nat) (mid : Config 284), 0<m ∧ mid.state=23 ∧
    Holds (cycleOut mid) 5 (encode [1,0]) ∧
    Holds (cycleOut mid) (-34) (markerWindow (List.replicate 13 0 ++ [1])) ∧
    silentSegment machine (machine.system.run 0) (cfg 93 (-34) (cycleOut mid))
      (2133669+m+67+76+10+20+29+39+135) := by
  obtain ⟨m,hm,hstart⟩ := blank_start_all_zero_return
  obtain ⟨mid,hs,hbank,hwindow,_hbefore,_hmark,hseg⟩ := unit_increment_reads_next
  exact ⟨m,mid,hm,hs,hbank,hwindow,
    segAdd machine _ _ _ (2133669+m+67+76+10+20+29+39) 135 hstart hseg⟩

#print axioms after_next_window
#print axioms unit_increment_reads_next
#print axioms blank_start_reads_next
end Shared.Beeping.NPcoNP.Bootstrap284UnitNext93
