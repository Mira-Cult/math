import Shared.Beeping.NPcoNP.Bootstrap284TerminalUnit
import Shared.Beeping.NPcoNP.NativeManyShift

/-! The reachable selector after the terminal unit return takes the
many-value branch and finishes its first pair shift. This remains a finite prefix. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ManyShift
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeTerminalUnitSelector
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeHalfMarkerMany
open Shared.Beeping.NPcoNP.NativeManyShift
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284Unit261Seed
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
open Shared.Beeping.NPcoNP.Bootstrap284TerminalUnit
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

def manySelector : List Nat := List.replicate 12 0 ++ [3,1]
def afterDispatch : Int → Bool := clearAt (-2) postReturn

theorem actual_window : Holds postReturn (-30) (markerWindow manySelector) := by
  have hw := left_window
  rw [terminal_window] at hw
  have he : markerWindow manySelector = false ::
      (encode (List.replicate 12 0) ++ [true,true,true,true,false,true,true]) := by decide
  rw [he]
  simp only [encode,List.replicate_succ,List.replicate_zero,block,List.cons_append,
    List.nil_append,Holds] at hw ⊢
  simp_all [postReturn,fillRange,setAt,terminal_marker,terminal_h0,terminal_h1]

theorem preceding_marker : postReturn (-31)=true := by
  have hw := left_window
  rw [terminal_window] at hw
  simp only [encode,List.replicate_succ,List.replicate_zero,block,List.cons_append,
    List.nil_append,Holds] at hw
  simpa [postReturn,fillRange,setAt] using hw.2.1

theorem dispatch_bit : postReturn (-2)=true := by
  rw [postReturn_eq]
  simpa only [setAt, if_neg (by decide : (-2 : Int) ≠ -3),
    if_neg (by decide : (-2 : Int) ≠ 6)] using returned_neg2

theorem first_word : Holds afterDispatch (-1) (List.replicate 0 true ++ [false]) := by
  have h := actual_q261_next_zero
  simp [afterDispatch,postReturn_eq,clearAt,setAt,Holds,h]

theorem second_word : Holds afterDispatch 0 (List.replicate 4 true ++ [false]) := by
  have h := actual_scanword
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds] at h ⊢
  simp_all [afterDispatch,postReturn_eq,clearAt,setAt]

theorem returned_eight : returnedTape 8=false := by
  unfold returnedTape currentTape
  rw [run_2133586]
  simp [fillRange,setAt,toConfig,cfg,bitSnapshot]

theorem shift_bits : afterDispatch 4=false ∧ afterDispatch 5=true ∧
    afterDispatch 6=true ∧ afterDispatch 7=false ∧ afterDispatch 8=false := by
  have h := actual_scanword
  have hb := actual_bank
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds] at h
  simp only [encode,block,List.replicate_succ,List.replicate_zero,List.cons_append,
    List.nil_append,Holds] at hb
  simp_all [afterDispatch,postReturn_eq,clearAt,setAt,returned_eight]

/-- The next 76 transitions after the checked state-83 visit are silent,
and the entire tape at state 23 is specified. -/
theorem checked_many_shift :
    silentSegment machine (cfg 83 1 postReturn)
      (cfg 23 3 (setAt 7 (clearAt 6 afterDispatch))) 76 := by
  have w : Holds postReturn (-30)
      (markerWindow (List.replicate 12 0 ++ 3::[1])) := by
    simpa [manySelector] using actual_window
  have s1 := marker_window_to93 postReturn (-30) manySelector (by decide) actual_window preceding_marker
  have s1' : silentSegment machine (cfg 83 1 postReturn) (cfg 93 (-30) postReturn) 33 := by
    simpa [manySelector,encode_append,encode,block,zeros_length] using s1
  have s2 := marker_window_to_ge_two postReturn (-30) 12 1 [1] (by decide) w
  have s2' : silentSegment machine (cfg 93 (-30) postReturn) (cfg 260 (-2) postReturn) 28 := by
    simpa using s2
  have s3 : silentSegment machine (cfg 260 (-2) postReturn) (cfg 15 (-1) afterDispatch) 1 := by
    simpa [afterDispatch] using oneSeg machine _ _ (step260_one (-2) postReturn dispatch_bit)
  have s4 := scans_and_shift 0 4 (-1) afterDispatch first_word second_word
    shift_bits.1 shift_bits.2.1 shift_bits.2.2.1 shift_bits.2.2.2.1 shift_bits.2.2.2.2
  have s4' : silentSegment machine (cfg 15 (-1) afterDispatch)
      (cfg 23 3 (setAt 7 (clearAt 6 afterDispatch))) 14 := by simpa using s4
  have s12 := segAdd machine _ _ _ 33 28 s1' s2'
  have s123 := segAdd machine _ _ _ 61 1 (by simpa using s12) s3
  have sall := segAdd machine _ _ _ 62 14 (by simpa using s123) s4'
  simpa using sall

/-- The same exact segment is reached on blank input after a positive finite
startup; the earlier return still has an existential duration. -/
theorem blank_start_many_shift : ∃ n : Nat, 0<n ∧
    silentSegment machine (machine.system.run 0)
      (cfg 23 3 (setAt 7 (clearAt 6 afterDispatch))) (2133669+n+67+76) := by
  obtain ⟨n,hn,hstart⟩ := blank_start_terminal_return
  exact ⟨n,hn,segAdd machine _ _ _ (2133669+n+67) 76 hstart checked_many_shift⟩

#print axioms checked_many_shift
#print axioms blank_start_many_shift
end Shared.Beeping.NPcoNP.Bootstrap284ManyShift
