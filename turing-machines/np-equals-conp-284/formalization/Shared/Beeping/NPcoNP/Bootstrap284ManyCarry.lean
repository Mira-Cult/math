import Shared.Beeping.NPcoNP.Bootstrap284ManyShift
import Shared.Beeping.NPcoNP.NativeHalfReturn23
import Shared.Beeping.NPcoNP.NativeHalfState1Scan

/-! The actual state-23 pair shift returns to the finite left carry.
This is a finite prefix and does not establish the recurring machine invariant. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ManyCarry
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfReturn23
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284TerminalUnit
open Shared.Beeping.NPcoNP.Bootstrap284ManyShift
open Shared.Beeping.NPcoNP.Bootstrap284Unit261Seed
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 9000000

def shiftedTape : Int → Bool := setAt 7 (clearAt 6 afterDispatch)

theorem return_word : downHolds shiftedTape 3 [true,true,true,true,false,false] := by
  have h := actual_scanword
  have hn := actual_q261_next_zero
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds] at h
  simp_all [shiftedTape,afterDispatch,postReturn_eq,setAt,clearAt,downHolds]

theorem carry_word : downHolds shiftedTape (-3) [true,true,true,false] := by
  have h := actual_window
  have he : markerWindow manySelector = false ::
      (encode (List.replicate 12 0) ++ [true,true,true,true,false,true,true]) := by decide
  rw [he] at h
  simp only [encode,List.replicate_succ,List.replicate_zero,block,List.cons_append,
    List.nil_append,Holds] at h
  simp_all [shiftedTape,afterDispatch,setAt,clearAt,downHolds]

theorem checked_return_to_carry :
    silentSegment machine (cfg 23 3 shiftedTape) (cfg 1 (-3) shiftedTape) 6 := by
  let shape := Shape.one (.one (.one (.one .stop)))
  have hw : downHolds shiftedTape 3 (bits shape ++ [false,false]) := by
    simpa [shape,bits] using return_word
  have hs := return_scan shape 3 shiftedTape hw
  simpa [shape,bits] using hs

theorem checked_carry_to27 :
    silentSegment machine (cfg 1 (-3) shiftedTape)
      (cfg 27 (-5) (result shiftedTape (-3) 3)) 4 := by
  have hw : downHolds shiftedTape (-3) (List.replicate 3 true ++ [false]) := by
    simpa using carry_word
  have hs := scan shiftedTape (-3) 3 hw
  simpa using hs

theorem blank_start_many_carry : ∃ n : Nat, 0<n ∧
    silentSegment machine (machine.system.run 0)
      (cfg 27 (-5) (result shiftedTape (-3) 3)) (2133669+n+67+76+10) := by
  obtain ⟨n,hn,hstart⟩ := blank_start_many_shift
  have hret := segAdd machine _ _ _ 6 4 checked_return_to_carry checked_carry_to27
  have hall := segAdd machine _ _ _ (2133669+n+67+76) 10 hstart (by simpa [shiftedTape] using hret)
  exact ⟨n,hn,by simpa only [shiftedTape] using hall⟩

#print axioms blank_start_many_carry
end Shared.Beeping.NPcoNP.Bootstrap284ManyCarry
