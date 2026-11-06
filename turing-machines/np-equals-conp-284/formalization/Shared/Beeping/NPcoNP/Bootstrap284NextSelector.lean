import Shared.Beeping.NPcoNP.Bootstrap284ManyCarry
import Shared.Beeping.NPcoNP.NativeHalfState27Scan
import Shared.Beeping.NPcoNP.NativeHalfMarkerExact

/-! Continue the checked blank-start many-selector carry to its next state-83
visit, and recover the exact fourteen-block selector window there. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284NextSelector
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState27Scan
open Shared.Beeping.NPcoNP.NativeHalfMarkerExact
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfState28Exit
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
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
set_option maxHeartbeats 16000000

def carryTape : Int → Bool := result shiftedTape (-3) 3
def scanTape : Int → Bool := put carryTape 0 false

theorem scan27_cells :
    (∀ i : Nat, i<5 → carryTape (-5+(i : Int))=false) ∧ carryTape 0=true := by
  have hw := carry_word
  have hs := actual_scanword
  have hz := actual_q261_next_zero
  simp only [downHolds] at hw
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds] at hs
  constructor
  · intro i hi
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [carryTape,result,cleared,put,shiftedTape,afterDispatch,clearAt,setAt,postReturn_eq]
  · simp_all [carryTape,result,cleared,put,shiftedTape,afterDispatch,clearAt,setAt,postReturn_eq]

theorem scan28_cells : scanTape (-6)=true ∧
    (∀ q, (-6:Int)<q → q<1 → scanTape q=false) ∧ scanTape 4=false := by
  have hs := scan27_cells
  have hw := carry_word
  have ha := actual_scanword
  have hz := actual_q261_next_zero
  simp only [downHolds] at hw
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds] at ha
  refine ⟨?_,?_,?_⟩
  · simp [scanTape,carryTape,result,put]
  · intro q hq hq'
    have h : q= -5 ∨ q= -4 ∨ q= -3 ∨ q= -2 ∨ q= -1 ∨ q=0 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [scanTape,carryTape,result,cleared,put,shiftedTape,afterDispatch,clearAt,setAt,postReturn_eq]
  · simp_all [scanTape,carryTape,result,cleared,put,shiftedTape,afterDispatch,clearAt,setAt,postReturn_eq]

/-- Exact output of the state-28 clear and state-6 write at this seed. -/
def nextTape : Int → Bool := put (clearRange scanTape 1 4) 3 true

theorem scan28_ones : ∀ i : Nat, i<3 → scanTape (1+(i : Int))=true := by
  have ha := actual_scanword
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds] at ha
  intro i hi
  have h : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases h with rfl | rfl | rfl <;>
    simp_all [scanTape,carryTape,result,cleared,put,shiftedTape,afterDispatch,clearAt,setAt,postReturn_eq]

/-- Unlike the general finite-return theorem, this seed takes exactly twenty
transitions from state 27 to state 83. -/
theorem exact_next_return :
    silentSegment machine (cfg 27 (-5) carryTape) (cfg 83 (-7) nextTape) 20 := by
  obtain ⟨hz,ho⟩ := scan27_cells
  have h27 : silentSegment machine (cfg 27 (-5) carryTape) (cfg 28 1 scanTape) 6 := by
    have hs := scan_to_one (-5) carryTape 5 hz (by simpa using ho)
    simpa [scanTape] using hs
  have h28 : silentSegment machine (cfg 28 1 scanTape)
      (cfg 6 3 (clearRange scanTape 1 4)) 4 := by
    have hs := scan28_exact 3 1 scanTape scan28_ones (by simpa using scan28_cells.2.2)
    simpa using hs
  have h3 : clearRange scanTape 1 4 3=false := by simp [clearRange]
  have h6 : silentSegment machine (cfg 6 3 (clearRange scanTape 1 4))
      (cfg 97 2 nextTape) 1 := by
    have hs := oneSeg machine _ _ (step6_zero 3 (clearRange scanTape 1 4) h3)
    simpa [nextTape] using hs
  have hm : nextTape (-6)=true := by simp [nextTape,put,clearRange,scan28_cells.1]
  have hc : ∀ q, (-6:Int)<q → q≤2 → nextTape q=false := by
    intro q hq hq'
    by_cases hq1 : q<1
    · have hz := scan28_cells.2.1 q hq hq1
      simpa [nextTape,put,clearRange,show q≠3 by omega,show ¬(1≤q ∧ q<4) by omega] using hz
    · simp [nextTape,put,clearRange,show q≠3 by omega,show 1≤q ∧ q<4 by omega]
  have h97 : silentSegment machine (cfg 97 2 nextTape) (cfg 83 (-7) nextTape) 9 := by
    have hs := scan97_corridor 8 2 (-6) nextTape (by norm_num) hm hc
    simpa using hs
  have hs := segAdd machine _ _ _ 6 4 h27 h28
  have hs' := segAdd machine _ _ _ 10 1 hs h6
  have hs'' := segAdd machine _ _ _ 11 9 hs' h97
  exact hs''

/-- The earlier concrete tape contains the fourteen zero blocks immediately
before the next carry marker, together with their left boundary marker. -/
theorem next_source_window :
    Holds postReturn (-34) (markerWindow (List.replicate 14 0)) ∧ postReturn (-35)=true := by
  have he : markerWindow (List.replicate 14 0) = [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] := by decide
  rw [he,postReturn_eq]
  unfold returnedTape currentTape
  rw [run_2133586]
  simp only [Holds]
  all_goals decide

/-- The explicit next tape agrees with the original source tape left of the
new marker and therefore has the recovered selector window. -/
theorem nextTape_window : nextTape (-6)=true ∧ nextTape (-35)=true ∧
    Holds nextTape (-34) (markerWindow (List.replicate 14 0)) := by
  have hframe : ∀ q, q< -6 → nextTape q=postReturn q := by
    intro q hq
    simp [nextTape,clearRange,scanTape,carryTape,result,cleared,put,shiftedTape,
      afterDispatch,clearAt,setAt, show q≠3 by omega, show ¬(1≤q ∧ q<4) by omega,
      show q≠0 by omega, show q≠ -6 by omega, show q≠7 by omega,
      show q≠6 by omega, show q≠ -2 by omega, show ¬((-6:Int)<q ∧ q≤ -3) by omega]
  have hm : nextTape (-6)=true := by
    simp [nextTape,put,clearRange,scan28_cells.1]
  refine ⟨hm,?_,?_⟩
  · rw [hframe (-35) (by omega)]
    exact next_source_window.2
  · apply holds_transport postReturn nextTape (-34) _ next_source_window.1
    intro q _ hq
    have hl : (markerWindow (List.replicate 14 0)).length=28 := by
      rw [markerWindow_length,zeros_length]
    rw [hl] at hq
    symm
    exact hframe q (by omega)

/-- The blank-start machine reaches the next state-93 selector with exact
local duration; only the earlier seed duration remains existential. -/
theorem blank_start_next_selector93_exact : ∃ m : Nat, 0<m ∧
    silentSegment machine (machine.system.run 0) (cfg 93 (-34) nextTape)
      (2133669+m+67+76+10+20+29) := by
  obtain ⟨m,hm,hstart⟩ := blank_start_many_carry
  have hstart' : silentSegment machine (machine.system.run 0)
      (cfg 27 (-5) carryTape) (2133669+m+67+76+10) := by simpa [carryTape] using hstart
  have he := marker_window_to93 nextTape (-34) (List.replicate 14 0)
    (by simp) nextTape_window.2.2 nextTape_window.2.1
  have he' : silentSegment machine (cfg 83 (-7) nextTape) (cfg 93 (-34) nextTape) 29 := by
    have hlen : (encode (List.replicate 14 0)).length=28 := by rw [zeros_length]
    simpa only [hlen,Nat.cast_ofNat,Int.reduceNeg,Int.reduceAdd,Int.reduceSub,Nat.reduceAdd] using he
  have h := segAdd machine _ _ _ (2133669+m+67+76+10) 20 hstart' exact_next_return
  exact ⟨m,hm,segAdd machine _ _ _ (2133669+m+67+76+10+20) 29 h he'⟩

#print axioms nextTape_window
#print axioms blank_start_next_selector93_exact
#print axioms exact_next_return
#print axioms next_source_window
end Shared.Beeping.NPcoNP.Bootstrap284NextSelector
