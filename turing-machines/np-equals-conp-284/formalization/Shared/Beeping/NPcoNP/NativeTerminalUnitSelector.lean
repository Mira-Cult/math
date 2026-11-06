import Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
import Shared.Beeping.NPcoNP.NativeHalfScannerReturns
import Shared.Beeping.NPcoNP.NativeHalfState10Progress
import Shared.Beeping.NPcoNP.NativeHalfMarkerTwoSafe
import Shared.Beeping.NPcoNP.NativeIncBank

/-! A last unit block whose omitted delimiter is occupied by a one marker.
Unlike a window with a following block, this takes the state-260 zero branch. -/
namespace Shared.Beeping.NPcoNP.NativeTerminalUnitSelector
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState93Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfMarkerTwoSafe
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

/-- A final unit block supplies two ones, excluding the delimiter at the
marker cell. -/
theorem terminal_window (z : Nat) :
    markerWindow (List.replicate z 0 ++ [1]) =
      false :: (encode (List.replicate z 0) ++ [true,true]) := by
  apply List.append_cancel_right (bs := [false])
  have h := markerWindow_append_zero (List.replicate z 0 ++ [1])
  simpa [encode_append,encode,block,List.append_assoc] using h

/-- A one at the omitted delimiter turns the terminal unit into the state-260
branch, which reads the following supplied zero. -/
theorem terminal_unit_to260 (t : Int → Bool) (a : Int) (z : Nat)
    (window : Holds t a (markerWindow (List.replicate z 0 ++ [1])))
    (marker : t (a+((2*z : Nat):Int)+3)=true)
    (nextZero : t (a+((2*z : Nat):Int)+4)=false) :
    silentSegment machine (cfg 93 a t)
      (cfg 260 (a+((2*z : Nat):Int)+4) t) (2*z+4) := by
  let word := markerWindow (List.replicate z 0 ++ [1])
  have hlen : word.length=2*z+3 := by
    simp [word,terminal_window,zeros_length]
  have pair : Holds t (a+(word.length : Int)) [true,false] := by
    rw [hlen]
    simp only [Nat.cast_add,Nat.cast_ofNat]
    have he : a+(((2*z : Nat):Int)+3)=a+((2*z : Nat):Int)+3 := by omega
    rw [he]
    change t (a+((2*z : Nat):Int)+3)=true ∧
      t (a+((2*z : Nat):Int)+3+1)=false ∧ True
    refine ⟨marker,?_,trivial⟩
    have he : a+((2*z : Nat):Int)+3+1=a+((2*z : Nat):Int)+4 := by omega
    rw [he]
    exact nextZero
  have all := holds_append_intro t a word [true,false] window pair
  have layout : Holds t a (false :: (encode (List.replicate z 0) ++ block 2)) := by
    simpa [word,terminal_window,block,List.append_assoc] using all
  have hfirst := oneSeg machine _ _ (step93_zero a t layout.1)
  have hscan := zero_blocks_then_ge_two t (a+1) z 0 [] (by simpa using layout.2)
  have hall := segAdd machine _ _ _ 1 (2*z+3) hfirst hscan
  have hp : a+1+((2*z : Nat):Int)+3 = a+((2*z : Nat):Int)+4 := by omega
  have hc : 1+(2*z+3)=2*z+4 := by omega
  simpa only [hp,hc] using hall

/-- Under an explicit later marker, this terminal selector safely passes
through state 10 and returns to state 83 in exact finite silent time. -/
theorem terminal_unit_fill_return (t : Int → Bool) (a : Int) (z k : Nat)
    (hk : 0<k)
    (window : Holds t a (markerWindow (List.replicate z 0 ++ [1])))
    (marker : t (a+((2*z : Nat):Int)+3)=true)
    (h0 : t (a+((2*z : Nat):Int)+4)=false)
    (h1 : t (a+((2*z : Nat):Int)+5)=false)
    (hz : ∀ i : Nat, i<k → t (a+((2*z : Nat):Int)+6+(i : Int))=false)
    (hm : t (a+((2*z : Nat):Int)+6+(k : Int))=true) :
    let d := a+((2*z : Nat):Int)+4
    let out := fillRange (setAt d t) (d+2) (d+2+(k : Int))
    silentSegment machine (cfg 93 a t) (cfg 83 (d+(k : Int)) out) (2*z+k+8) := by
  dsimp only
  let d := a+((2*z : Nat):Int)+4
  let t1 := setAt d t
  have h260 := terminal_unit_to260 t a z window marker h0
  have hstep := oneSeg machine _ _ (step260_zero d t h0)
  have h42read : t1 (d+1)=false := by
    change (if d+1=d then true else t (d+1))=false
    rw [if_neg (by omega)]
    have he : d+1=a+((2*z : Nat):Int)+5 := by dsimp [d]; omega
    rw [he]
    exact h1
  have h42 := oneSeg machine _ _ (step42_zero (d+1) t1 h42read)
  have hz' : ∀ i : Nat, i<k → t1 (d+2+(i : Int))=false := by
    intro i hi
    change (if d+2+(i : Int)=d then true else t (d+2+(i : Int)))=false
    rw [if_neg (by omega)]
    have he : d+2+(i : Int)=a+((2*z : Nat):Int)+6+(i : Int) := by dsimp [d]; omega
    rw [he]
    exact hz i hi
  have hm' : t1 (d+2+(k : Int))=true := by
    change (if d+2+(k : Int)=d then true else t (d+2+(k : Int)))=true
    rw [if_neg (by omega)]
    have he : d+2+(k : Int)=a+((2*z : Nat):Int)+6+(k : Int) := by dsimp [d]; omega
    rw [he]
    exact hm
  have h10 := scan10_return83 k (d+2) t1 hk hz' hm'
  have hbefore := segAdd machine _ _ _ (2*z+4) 1 h260 hstep
  have hbefore' := segAdd machine _ _ _ (2*z+4+1) 1 hbefore h42
  have hpre : silentSegment machine (cfg 93 a t) (cfg 10 (d+2) t1) (2*z+4+1+1) := by
    have hp : d+1+1=d+2 := by omega
    simpa only [hp] using hbefore'
  have hall := segAdd machine _ _ _ (2*z+4+1+1) (k+2) hpre h10
  have hp : d+2+(k : Int)-2=d+(k : Int) := by omega
  have hc : 2*z+4+1+1+(k+2)=2*z+k+8 := by omega
  simpa only [hp,hc,d,t1] using hall

#print axioms terminal_unit_to260
#print axioms terminal_unit_fill_return
end Shared.Beeping.NPcoNP.NativeTerminalUnitSelector
