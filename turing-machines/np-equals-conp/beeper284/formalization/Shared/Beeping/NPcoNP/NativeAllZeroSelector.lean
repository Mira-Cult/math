import Shared.Beeping.NPcoNP.NativeTerminalUnitSelector

/-! All-zero marker windows: the carry marker completes the last unit
block, so a supplied zero after it chooses the state-261 dispatch. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroSelector
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState93Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerReturns
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfWindowZeroScan
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- The final unary zero block loses its delimiter in the marker window. -/
theorem all_zero_window (k : Nat) :
    markerWindow (List.replicate k 0 ++ [0]) =
      false :: (encode (List.replicate k 0) ++ [true]) := by
  apply List.append_cancel_right (bs := [false])
  have h := markerWindow_append_zero (List.replicate k 0 ++ [0])
  simpa [encode_append,encode,block,List.append_assoc] using h

/-- The one marker joins the last block; the next zero chooses state 261.
All transitions are silent and the tape is unchanged. -/
theorem all_zero_to261 (t : Int → Bool) (a : Int) (k : Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ [0])))
    (marker : t (a+((2*k : Nat):Int)+2)=true)
    (nextZero : t (a+((2*k : Nat):Int)+3)=false) :
    silentSegment machine (cfg 93 a t)
      (cfg 261 (a+((2*k : Nat):Int)+4) t) (2*k+4) := by
  let word := markerWindow (List.replicate k 0 ++ [0])
  have hlen : word.length=2*k+2 := by simp [word,all_zero_window,zeros_length]
  have pair : Holds t (a+(word.length : Int)) [true,false] := by
    rw [hlen]
    simp only [Nat.cast_add,Nat.cast_ofNat]
    have he : a+(((2*k : Nat):Int)+2)=a+((2*k : Nat):Int)+2 := by omega
    rw [he]
    change t (a+((2*k : Nat):Int)+2)=true ∧
      t (a+((2*k : Nat):Int)+2+1)=false ∧ True
    refine ⟨marker,?_,trivial⟩
    have he : a+((2*k : Nat):Int)+2+1=a+((2*k : Nat):Int)+3 := by omega
    rw [he]
    exact nextZero
  have all := holds_append_intro t a word [true,false] window pair
  have layout : Holds t a (false :: (encode (List.replicate k 0) ++ block 1)) := by
    simpa [word,all_zero_window,block,List.append_assoc] using all
  have hfirst := oneSeg machine _ _ (step93_zero a t layout.1)
  have hscan := zero_blocks_then_one t (a+1) k [] (by simpa using layout.2)
  have hall := segAdd machine _ _ _ 1 (2*k+3) hfirst hscan
  have hp : a+1+((2*k : Nat):Int)+3 = a+((2*k : Nat):Int)+4 := by omega
  have hc : 1+(2*k+3)=2*k+4 := by omega
  simpa only [hp,hc] using hall

/-- A finite nonempty zero run and a later one complete the subsequent
state-261 fill and return, with its exact tape and timing. -/
theorem all_zero_fill_return (t : Int → Bool) (a : Int) (k r : Nat)
    (hr : 0<r)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ [0])))
    (marker : t (a+((2*k : Nat):Int)+2)=true)
    (nextZero : t (a+((2*k : Nat):Int)+3)=false)
    (h0 : t (a+((2*k : Nat):Int)+4)=false)
    (h1 : t (a+((2*k : Nat):Int)+5)=false)
    (hz : ∀ i : Nat, i<r → t (a+((2*k : Nat):Int)+6+(i : Int))=false)
    (hm : t (a+((2*k : Nat):Int)+6+(r : Int))=true) :
    let d := a+((2*k : Nat):Int)+4
    let out := fillRange (setAt d t) (d+2) (d+2+(r : Int))
    silentSegment machine (cfg 93 a t) (cfg 83 (d+(r : Int)) out) (2*k+r+8) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let t1 := setAt d t
  have h261 := all_zero_to261 t a k window marker nextZero
  have hstep := oneSeg machine _ _ (step261_zero d t h0)
  have h42read : t1 (d+1)=false := by
    change (if d+1=d then true else t (d+1))=false
    rw [if_neg (by omega)]
    have he : d+1=a+((2*k : Nat):Int)+5 := by dsimp [d]; omega
    rw [he]
    exact h1
  have h42 := oneSeg machine _ _ (step42_zero (d+1) t1 h42read)
  have hz' : ∀ i : Nat, i<r → t1 (d+2+(i : Int))=false := by
    intro i hi
    change (if d+2+(i : Int)=d then true else t (d+2+(i : Int)))=false
    rw [if_neg (by omega)]
    have he : d+2+(i : Int)=a+((2*k : Nat):Int)+6+(i : Int) := by dsimp [d]; omega
    rw [he]
    exact hz i hi
  have hm' : t1 (d+2+(r : Int))=true := by
    change (if d+2+(r : Int)=d then true else t (d+2+(r : Int)))=true
    rw [if_neg (by omega)]
    have he : d+2+(r : Int)=a+((2*k : Nat):Int)+6+(r : Int) := by dsimp [d]; omega
    rw [he]
    exact hm
  have h10 := scan10_return83 r (d+2) t1 hr hz' hm'
  have hbefore := segAdd machine _ _ _ (2*k+4) 1 h261 hstep
  have hbefore' := segAdd machine _ _ _ (2*k+4+1) 1 hbefore h42
  have hpre : silentSegment machine (cfg 93 a t) (cfg 10 (d+2) t1) (2*k+4+1+1) := by
    have hp : d+1+1=d+2 := by omega
    simpa only [hp] using hbefore'
  have hall := segAdd machine _ _ _ (2*k+4+1+1) (r+2) hpre h10
  have hp : d+2+(r : Int)-2=d+(r : Int) := by omega
  have hc : 2*k+4+1+1+(r+2)=2*k+r+8 := by omega
  simpa only [hp,hc,d,t1] using hall

#print axioms all_zero_window
#print axioms all_zero_to261
#print axioms all_zero_fill_return
end Shared.Beeping.NPcoNP.NativeAllZeroSelector
