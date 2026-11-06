import Shared.Beeping.NPcoNP.Bootstrap284NextBankExact
import Shared.Beeping.NPcoNP.NativeHalfReturn23
import Shared.Beeping.NPcoNP.NativeHalfState1Scan
import Shared.Beeping.NPcoNP.NativeHalfState27Scan
import Shared.Beeping.NPcoNP.NativeHalfState28Exit
import Shared.Beeping.NPcoNP.NativeHalfMarkerExact

/-! Continue the checked blank-start bank update through its physical return.
This is one finite bootstrap segment, not a recurrent simulation. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284NextReturnExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfReturn23
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState27Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfState28Exit
open Shared.Beeping.NPcoNP.NativeHalfMarkerExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.Bootstrap284TerminalFullExact
open Shared.Beeping.NPcoNP.Bootstrap284NextBankExact
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000
attribute [local irreducible] terminalTape

/-- The exact return reads six ones and then the first zero pair. -/
theorem return_word : downHolds nextBankTape 3
    [true,true,true,true,true,true,false,false] := by
  have hw := exact_next_window.1
  have he := exact_extension
  have hf := next_bank_segment.2.1
  simp only [markerWindow,encode,block,List.replicate_succ,List.replicate_zero,
    List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,List.append_assoc,
    Holds] at hw
  simp only [List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append,Holds] at he
  have hm4 : nextBankTape (-4)=false := by
    simp [nextBankTape,Shared.Beeping.NPcoNP.NativeHalfSweep.spec,
      Shared.Beeping.NPcoNP.NativeHalfState16Progress.clearAt]
  simp only [downHolds]
  repeat' constructor
  all_goals first | exact hm4 | (rw [hf _ (by omega) (by omega)]; simp_all) | trivial

/-- The carry starts with three ones and then a zero. -/
theorem carry_word : downHolds nextBankTape (-5) [true,true,true,false] := by
  have hw := exact_next_window.1
  have hf := next_bank_segment.2.1
  simp only [markerWindow,encode,block,List.replicate_succ,List.replicate_zero,
    List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,List.append_assoc,
    Holds] at hw
  simp only [downHolds]
  repeat' constructor
  all_goals first | (rw [hf _ (by omega) (by omega)]; simp_all) | trivial

def carryTape : Int → Bool := result nextBankTape (-5) 3
def scanTape : Int → Bool := put carryTape (-2) false
def returnTape : Int → Bool := put (clearRange scanTape (-1) 4) 3 true

theorem scan27_cells :
    (∀ i : Nat, i<5 → carryTape (-7+(i : Int))=false) ∧ carryTape (-2)=true := by
  have hw := carry_word
  have hr := return_word
  simp only [downHolds] at hw hr
  constructor
  · intro i hi
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl <;> simp_all [carryTape,result,cleared,put]
  · simp_all [carryTape,result,cleared,put]

theorem scan28_cells : scanTape (-8)=true ∧
    (∀ q, (-8:Int)<q → q< -1 → scanTape q=false) ∧ scanTape 4=false ∧
    (∀ i : Nat, i<5 → scanTape (-1+(i : Int))=true) := by
  have hc := carry_word
  have hr := return_word
  have hs := scan27_cells
  have he := exact_extension
  simp only [downHolds] at hc hr
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds] at he
  refine ⟨?_,?_,?_,?_⟩
  · simp [scanTape,carryTape,result,put]
  · intro q hq hq'
    have h : q= -7 ∨ q= -6 ∨ q= -5 ∨ q= -4 ∨ q= -3 ∨ q= -2 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [scanTape,carryTape,result,cleared,put]
  · have hf := next_bank_segment.2.1 4 (by omega) (by omega)
    have h4 : nextBankTape 4=false := by rw [hf]; simpa using he.2.2.1
    simpa [scanTape,carryTape,result,cleared,put] using h4
  · intro i hi
    have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [scanTape,carryTape,result,cleared,put]

/-- The actual state-23 configuration reaches state 83 after 36 silent
transitions, with the complete resulting tape specified. -/
theorem next_return_segment :
    silentSegment machine (cfg 23 3 nextBankTape) (cfg 83 (-9) returnTape) 36 := by
  let shape := Shape.one (.one (.one (.one (.one (.one .stop)))))
  have hword : downHolds nextBankTape 3 (bits shape ++ [false,false]) := by
    simpa [shape,bits] using return_word
  have h23 : silentSegment machine (cfg 23 3 nextBankTape) (cfg 1 (-5) nextBankTape) 8 := by
    simpa [shape,bits] using return_scan shape 3 nextBankTape hword
  have h1 : silentSegment machine (cfg 1 (-5) nextBankTape) (cfg 27 (-7) carryTape) 4 := by
    have hw : downHolds nextBankTape (-5) (List.replicate 3 true ++ [false]) := by
      simpa using carry_word
    simpa [carryTape] using scan nextBankTape (-5) 3 hw
  have h27 : silentSegment machine (cfg 27 (-7) carryTape) (cfg 28 (-1) scanTape) 6 := by
    simpa [scanTape] using scan_to_one (-7) carryTape 5 scan27_cells.1 (by simpa using scan27_cells.2)
  have h28 : silentSegment machine (cfg 28 (-1) scanTape)
      (cfg 6 3 (clearRange scanTape (-1) 4)) 6 := by
    simpa using scan28_exact 5 (-1) scanTape scan28_cells.2.2.2 scan28_cells.2.2.1
  have h6 : silentSegment machine (cfg 6 3 (clearRange scanTape (-1) 4))
      (cfg 97 2 returnTape) 1 := by
    have hz : clearRange scanTape (-1) 4 3=false := by simp [clearRange]
    simpa [returnTape] using oneSeg machine _ _ (step6_zero 3 _ hz)
  have hm : returnTape (-8)=true := by simp [returnTape,put,clearRange,scan28_cells.1]
  have hc : ∀ q, (-8:Int)<q → q≤2 → returnTape q=false := by
    intro q hq hq'
    by_cases hl : q< -1
    · have hh := scan28_cells.2.1 q hq hl
      simpa [returnTape,put,clearRange,show q≠3 by omega,
        show ¬((-1:Int)≤q ∧ q<4) by omega] using hh
    · simp [returnTape,put,clearRange,show q≠3 by omega,
        show (-1:Int)≤q ∧ q<4 by omega]
  have h97 : silentSegment machine (cfg 97 2 returnTape) (cfg 83 (-9) returnTape) 11 := by
    simpa using scan97_corridor 10 2 (-8) returnTape (by norm_num) hm hc
  have ha := segAdd machine _ _ _ 8 4 h23 h1
  have hb := segAdd machine _ _ _ 12 6 ha h27
  have hc' := segAdd machine _ _ _ 18 6 hb h28
  have hd := segAdd machine _ _ _ 24 1 hc' h6
  exact segAdd machine _ _ _ 25 11 hd h97

/-- The exact return is part of the actual blank-start run, with no events
in the full prefix. -/
theorem blank_start_next_return_exact :
    machine.system.run 2134219=cfg 83 (-9) returnTape ∧
    silentSegment machine (machine.system.run 0) (cfg 83 (-9) returnTape) 2134219 := by
  have hs := segAdd machine _ _ _ 2134183 36 blank_start_next_bank_exact.2.2.2 next_return_segment
  exact ⟨run_of_initial_segment 2134219 _ hs,hs⟩

#print axioms next_return_segment
#print axioms blank_start_next_return_exact
end Shared.Beeping.NPcoNP.Bootstrap284NextReturnExact
