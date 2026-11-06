import Shared.Beeping.NPcoNP.Bootstrap284SecondReturnExact
import Shared.Beeping.NPcoNP.NativeHalfSelectorExact

/-! Exact physical timing of the second checked dispatch and return, obtained
by composing the generic fill and selector-block theorems with the verified
bootstrap tape. This finite segment is not an all-run simulation. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerReturns
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnExact

set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

def currentTape : Int → Bool := (machine.system.run 2133586).tape
def returnedTape : Int → Bool := fillRange (setAt (-2) currentTape) 0 3
def selectorCounts : List Nat := [2,1,2] ++ List.replicate 11 1

theorem selector_counts_length : selectorCounts.length=14 := by decide
theorem selector_bits_length : (blocks selectorCounts).length=30 := by decide

/-- The finite cells used by the selector, checked against the literal
bootstrap snapshot and the proved exact fill operation. -/
theorem selector_input : downHolds returnedTape 1 (blocks selectorCounts) := by
  unfold returnedTape currentTape
  rw [run_2133586]
  simp only [selectorCounts,blocks,List.replicate_succ,List.replicate_zero,
    List.cons_append,List.nil_append,downHolds]
  all_goals decide

theorem selector_exit_marker : returnedTape (-29)=true := by
  unfold returnedTape currentTape
  rw [run_2133586]
  decide

/-- At the second state-261 dispatch, the actual table reaches state 93 at
head -28 in exactly 38 silent transitions with the stated whole tape. -/
theorem second_return_segment :
    silentSegment machine (machine.system.run 2133586)
      (cfg 93 (-28) returnedTape) 38 := by
  have h0 : currentTape (-2)=false := zero_neg2
  have hother (p : Int) (hp : p≠ -2) : setAt (-2) currentTape p=currentTape p := by
    simp only [setAt,if_neg hp]
  have h1 : setAt (-2) currentTape (-1)=false := by
    rw [hother (-1) (by decide)]
    exact zero_neg1
  have hz : ∀ i : Nat, i<3 → setAt (-2) currentTape (0+(i : Int))=false := by
    intro i hi
    have hi' : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi' with rfl | rfl | rfl
    · change setAt (-2) currentTape 0=false
      rw [hother 0 (by decide)]
      exact zero_0
    · change setAt (-2) currentTape 1=false
      rw [hother 1 (by decide)]
      exact zero_1
    · change setAt (-2) currentTape 2=false
      rw [hother 2 (by decide)]
      exact zero_2
  have hm : setAt (-2) currentTape (0+(3 : Int))=true := by
    change setAt (-2) currentTape 3=true
    rw [hother 3 (by decide)]
    exact one_3
  have hfirst := oneSeg machine _ _ (step261_zero (-2) currentTape h0)
  have hsecond := oneSeg machine _ _ (step42_zero (-1) (setAt (-2) currentTape) h1)
  have hdispatch : silentSegment machine (cfg 261 (-2) currentTape)
      (cfg 10 0 (setAt (-2) currentTape)) 2 := by
    simpa using segAdd machine _ _ _ 1 1 hfirst hsecond
  have hscan : silentSegment machine (cfg 10 0 (setAt (-2) currentTape))
      (cfg 83 1 returnedTape) 5 := by
    simpa only [returnedTape,Int.zero_add,Nat.cast_ofNat,Int.reduceSub,Nat.reduceAdd] using
      scan10_return83 3 0 (setAt (-2) currentTape) (by decide) hz hm
  have hin : downHolds returnedTape 1 (blocks selectorCounts ++ []) := by
    simpa using selector_input
  have hchain := (chain_blocks chain83 selectorCounts 1 returnedTape [] selector_counts_length hin).2
  have hchain' : silentSegment machine (cfg 83 1 returnedTape) (cfg 92 (-29) returnedTape) 30 := by
    simpa only [selector_bits_length,Nat.cast_ofNat,Int.reduceSub] using hchain
  have hexit : silentSegment machine (cfg 92 (-29) returnedTape) (cfg 93 (-28) returnedTape) 1 := by
    simpa only [Int.reduceAdd] using oneSeg machine _ _ (step92_one (-29) returnedTape selector_exit_marker)
  have hpref := segAdd machine _ _ _ 2 5 hdispatch hscan
  have hmore := segAdd machine _ _ _ 30 1 hchain' hexit
  have hall := segAdd machine _ _ _ 7 31 hpref hmore
  have hc : machine.system.run 2133586 = cfg 261 (-2) currentTape := by
    have hs := state261
    have hh := head_neg2
    cases he : machine.system.run 2133586 with
    | mk state head tape =>
      simp only [he,cfg] at hs hh ⊢
      simp only [currentTape,he,cfg] at *
      cases hs
      cases hh
      rfl
  simpa only [hc] using hall

/-- The entire blank-start prefix through that exact return is silent. -/
theorem blank_start_timed_return :
    silentSegment machine (machine.system.run 0) (cfg 93 (-28) returnedTape) 2133624 := by
  have h := segAdd machine _ _ _ 2133586 38 blank_start_66 (by
    rw [← run_2133586]
    exact second_return_segment)
  simpa using h

end Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed

#print axioms Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed.blank_start_timed_return
