import Shared.Beeping.NPcoNP.NativeAllZeroAbsentDispatch
import Shared.Beeping.NPcoNP.NativeAllZeroSelector

/-! Continue the marker-absent all-zero cycle through its next selector.
This is a supplied-window result and does not establish blank-start reachability. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroAbsentTo261
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeAllZeroSelector
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentDispatch
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

theorem absent_window_split :
    (markerWindow (List.replicate 13 0 ++ [0])).drop 2 ++ [true,false] =
      markerWindow (List.replicate 12 0 ++ [0]) ++ [true,false] := by decide

/-- The changed window immediately selects state 261 in 28 silent steps,
without changing the tape. -/
theorem absent_window_to261 (t : Int → Bool) (a : Int)
    (window : Holds t a ((markerWindow (List.replicate 13 0 ++ [0])).drop 2 ++ [true,false])) :
    silentSegment machine (cfg 93 a t) (cfg 261 (a+28) t) 28 := by
  let small := markerWindow (List.replicate 12 0 ++ [0])
  have hword : Holds t a (small ++ [true,false]) := by
    rw [absent_window_split] at window
    exact window
  have hprefix : Holds t a small := holds_prefix_word t a small [true,false] hword
  have hlen : small.length=26 := by decide
  have hpair := holds_append_tail t a small [true,false] hword
  rw [hlen] at hpair
  change t (a+26)=true ∧ t (a+26+1)=false ∧ True at hpair
  have hm : t (a+((2*12 : Nat):Int)+2)=true := by
    have he : a+((2*12 : Nat):Int)+2=a+26 := by norm_num; omega
    rw [he]
    exact hpair.1
  have hn : t (a+((2*12 : Nat):Int)+3)=false := by
    have he : a+((2*12 : Nat):Int)+3=a+26+1 := by norm_num; omega
    rw [he]
    exact hpair.2.1
  have h := all_zero_to261 t a 12 hprefix hm hn
  have he : a+((2*12 : Nat):Int)+4=a+28 := by norm_num; omega
  simpa only [he, show 2*12+4=28 by decide] using h

/-- Compose the padded marker-absent cycle through the subsequent
state-261 dispatch, preserving its bank and protected left tape. -/
theorem all_zero_padded_absent_to261 (a : Int) (r v : Nat) (rest : List Nat)
    (suffix : List Bool) (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
    (absent : t (a-3)=false)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int))
      ((encode (v::rest) ++ [false,false,false]) ++ ([false,false] ++ suffix))) :
    ∃ mid : Config 284, mid.state=23 ∧
      let t1 := setAt (a+29) (setAt (a+30) mid.tape)
      let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
      silentSegment machine (cfg 93 a t) (cfg 261 (a+28) final)
        (((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28) ∧
      Holds final a ((markerWindow (List.replicate 13 0 ++ [0])).drop 2 ++ [true,false]) ∧
      Holds final (a+36+(r : Int))
        ((encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix) ∧
      (∀ q, q<a+26 → final q=t q) := by
  obtain ⟨mid,hs,hseg,hwindow,hbank,hleft⟩ :=
    all_zero_padded_absent_dispatch a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  let t1 := setAt (a+29) (setAt (a+30) mid.tape)
  let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  have hnext := absent_window_to261 final a hwindow
  have hall := segAdd machine _ _ _
    ((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
      ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
      ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31) 28 hseg hnext
  exact ⟨mid,hs,hall,hwindow,hbank,hleft⟩

#print axioms all_zero_padded_absent_to261
#print axioms absent_window_split
#print axioms absent_window_to261
end Shared.Beeping.NPcoNP.NativeAllZeroAbsentTo261
