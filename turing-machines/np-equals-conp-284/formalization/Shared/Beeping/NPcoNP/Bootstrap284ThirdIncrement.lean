import Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
import Shared.Beeping.NPcoNP.NativeHalfState12Progress
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
import Shared.Beeping.NPcoNP.NativeIncBank

/-! Bind the second checked selector return to its next physical increment.
This finite actual-run result does not establish a graph simulation. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ThirdIncrement
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState12Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- A finite word held downwards also holds in reverse when read upwards. -/
theorem down_reverse_holds (t : Int → Bool) (h : Int) (xs : List Bool)
    (hd : downHolds t h xs) :
    Holds t (h-((xs.length : Nat):Int)+1) xs.reverse := by
  induction xs generalizing h with
  | nil => trivial
  | cons b xs ih =>
    change t h=b ∧ downHolds t (h-1) xs at hd
    have hh := ih (h-1) hd.2
    have hp : h-1-((xs.length : Nat):Int)+1 = h-((xs.length : Nat):Int) := by omega
    rw [hp] at hh
    have hcell : Holds t ((h-((xs.length : Nat):Int)) + (xs.reverse.length : Int)) [b] := by
      simp only [List.length_reverse]
      have he : h-((xs.length : Nat):Int)+((xs.length : Nat):Int)=h := by omega
      rw [he]
      exact ⟨hd.1,trivial⟩
    have hall := holds_append_intro t (h-((xs.length : Nat):Int)) xs.reverse [b] hh hcell
    have he : h-(((b::xs).length : Nat):Int)+1=h-((xs.length : Nat):Int) := by simp; omega
    simpa only [List.reverse_cons,he] using hall

def selector : List Nat := List.replicate 11 0 ++ [1,0,1]

theorem actual_window : Holds returnedTape (-28) (markerWindow selector) := by
  have h := down_reverse_holds returnedTape 1 (blocks selectorCounts) selector_input
  have he : (blocks selectorCounts).reverse=markerWindow selector := by decide
  rw [selector_bits_length,he] at h
  simpa using h

/-- The checked state-93 visit takes the unit selector to state 12 with an
exactly located control write. -/
theorem actual_selector_to12 :
    silentSegment machine (cfg 93 (-28) returnedTape)
      (cfg 12 0 (clearAt (-2) returnedTape)) 28 := by
  have hw : Holds returnedTape (-28)
      (markerWindow (List.replicate 11 0 ++ 1::0::1::[])) := by
    simpa [selector] using actual_window
  have h := marker_unit_to12 returnedTape (-28) 11 0 1 [] hw
  simpa using h

/-- The scan past the actual finite one-run reaches state 14 at cell 5. -/
theorem actual_selector_to14 :
    silentSegment machine (cfg 93 (-28) returnedTape)
      (cfg 14 5 (clearAt (-2) returnedTape)) 33 := by
  have ht : Holds (clearAt (-2) returnedTape) 0
      (List.replicate 4 true ++ [false]) := by
    unfold clearAt returnedTape currentTape
    rw [run_2133586]
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds]
    all_goals decide
  have hscan : silentSegment machine (cfg 12 0 (clearAt (-2) returnedTape))
      (cfg 14 5 (clearAt (-2) returnedTape)) 5 := by
    simpa using Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14.scan12 4 0 _ ht
  have h := segAdd machine _ _ _ 28 5 actual_selector_to12 hscan
  simpa using h

/-- The literal blank-start run reaches this state-14 configuration at the
exact time, with the complete tape and all previous events silent. -/
theorem blank_start_to14 :
    silentSegment machine (machine.system.run 0)
      (cfg 14 5 (clearAt (-2) returnedTape)) 2133657 := by
  have h := segAdd machine _ _ _ 2133624 33 blank_start_timed_return actual_selector_to14
  simpa using h

theorem actual_increment_bank :
    Holds (clearAt (-2) returnedTape) 5 (encode [0] ++ [false]) := by
  unfold clearAt returnedTape currentTape
  rw [run_2133586]
  simp only [encode,block,List.replicate_succ,List.replicate_zero,List.cons_append,
    List.nil_append,Holds]
  all_goals decide

/-- The complete post-increment tape is the old tape with cell 6 set;
the source and all off-window cells are identified, not just its state. -/
theorem blank_start_third_increment_exact :
    silentSegment machine (machine.system.run 0)
      (cfg 23 6 (setAt 6 (clearAt (-2) returnedTape))) 2133660 := by
  let t := clearAt (-2) returnedTape
  obtain ⟨mid,hstate,hhead,hbank,hframe,hseg⟩ :=
    encoded_increment 0 [] 5 t actual_increment_bank
  have hhead' : mid.head=6 := by simpa [encode] using hhead
  have hcells : mid.tape 5=true ∧ mid.tape 6=true := by
    have hb : mid.tape 5=true ∧ mid.tape 6=true ∧ mid.tape 7=false := by
      simpa [encode,block,Holds] using hbank
    exact ⟨hb.1,hb.2.1⟩
  have hin : t 5=true := by
    have h := actual_increment_bank
    simpa [encode,block,Holds] using h.1
  have htape : mid.tape=setAt 6 t := by
    funext p
    by_cases h6 : p=6
    · subst p
      simp [setAt,hcells.2]
    · by_cases h5 : p=5
      · subst p
        simp [setAt,hcells.1,hin]
      · have hr : p<5 ∨ 6<p := by omega
        have hf := hframe p (by simpa [encode] using hr)
        simp [setAt,h6,hf]
  have hc : mid=cfg 23 6 (setAt 6 t) := by
    have hi : mid=cfg mid.state mid.head mid.tape := by cases mid; rfl
    simpa only [hstate,hhead',htape] using hi
  have h := segAdd machine _ _ _ 2133657 (0+3+(encode ([] : List Nat)).length) blank_start_to14 hseg
  rw [hc] at h
  simpa [encode,t] using h

theorem run_2133660 : machine.system.run 2133660 =
    cfg 23 6 (setAt 6 (clearAt (-2) returnedTape)) :=
  Shared.Beeping.NPcoNP.Bootstrap284RunBridge.run_of_initial_segment 2133660 _ blank_start_third_increment_exact

#print axioms blank_start_third_increment_exact
#print axioms run_2133660
#print axioms down_reverse_holds
#print axioms actual_window
#print axioms blank_start_to14
end Shared.Beeping.NPcoNP.Bootstrap284ThirdIncrement
