import Shared.Beeping.NPcoNP.NativeHalfState93Progress
import Shared.Beeping.NPcoNP.NativeFirstZeroOperation
import Shared.Beeping.NPcoNP.NativeHalfScannerReturns

/-! The short, exceptional control path from a marker at state 93. -/
namespace Shared.Beeping.NPcoNP.NativeTerminalMarkerFill
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState93Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerReturns
open Shared.Beeping.NPcoNP.NativeFirstZeroOperation
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
theorem row259_zero : machine.table.row 259 false = ⟨false,.right,99,false⟩ := by decide
theorem row99_zero : machine.table.row 99 false = ⟨true,.right,9,false⟩ := by decide

attribute [local irreducible] machine

theorem step259_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 259 h t)=(cfg 99 (h+1) t,false) := by
  have hw : (⟨259,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row259_zero,Move.apply,hw]

theorem step99_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 99 h t)=(cfg 9 (h+1) (setAt h t),false) := by
  have hw : (⟨99,h,t⟩ : Config 284).write true=setAt h t := rfl
  simp [cfg,Machine.step,ht,row99_zero,Move.apply,hw]

/-- The marker, finite zero corridor and following one give an exact silent
scan to state 83, including the tape updates. -/
theorem terminal_marker_fill (t : Int → Bool) (a : Int) (r : Nat) (hr : 0<r)
    (mark : t a=true) (zeros : ∀ q, a<q → q<a+6+(r : Int) → t q=false)
    (stop : t (a+6+(r : Int))=true) :
    silentSegment machine (cfg 93 a t)
      (cfg 83 (a+6+(r : Int)-2) (fillRange (setAt (a+3) t) (a+6) (a+6+(r : Int)))) (r+8) := by
  have h1 : t (a+1)=false := zeros _ (by omega) (by omega)
  have h2 : t (a+2)=false := zeros _ (by omega) (by omega)
  have h3 : t (a+3)=false := zeros _ (by omega) (by omega)
  have h4 : t (a+4)=false := zeros _ (by omega) (by omega)
  have h5 : t (a+5)=false := zeros _ (by omega) (by omega)
  have hput : put t (a+1) false=t := by
    funext q
    by_cases hq : q=a+1
    · subst q; simp [put,h1]
    · simp [put,hq]
  let u := setAt (a+3) t
  have hu4 : u (a+4)=false := by simpa [u,setAt,show a+4≠a+3 by omega] using h4
  have hu5 : u (a+5)=false := by simpa [u,setAt,show a+5≠a+3 by omega] using h5
  have hfirst := oneSeg machine _ _ (step93_one a t mark)
  have hsecond : silentSegment machine (cfg 94 (a+1) t) (cfg 259 (a+2) t) 1 := by
    simpa only [hput,show a+1+1=a+2 by omega] using oneSeg machine _ _ (step94 (a+1) t)
  have hthird : silentSegment machine (cfg 259 (a+2) t) (cfg 99 (a+3) t) 1 := by
    simpa only [show a+2+1=a+3 by omega] using oneSeg machine _ _ (step259_zero (a+2) t h2)
  have hfourth : silentSegment machine (cfg 99 (a+3) t) (cfg 9 (a+4) u) 1 := by
    simpa only [u,show a+3+1=a+4 by omega] using oneSeg machine _ _ (step99_zero (a+3) t h3)
  have hfifth : silentSegment machine (cfg 9 (a+4) u) (cfg 42 (a+5) u) 1 := by
    simpa only [show a+4+1=a+5 by omega] using oneSeg machine _ _ (step9_zero (a+4) u hu4)
  have hsixth : silentSegment machine (cfg 42 (a+5) u) (cfg 10 (a+6) u) 1 := by
    simpa only [show a+5+1=a+6 by omega] using oneSeg machine _ _ (step42_zero (a+5) u hu5)
  have hpref : silentSegment machine (cfg 93 a t) (cfg 10 (a+6) u) 6 := by
    exact segAdd machine _ _ _ 5 1 (segAdd machine _ _ _ 4 1
      (segAdd machine _ _ _ 3 1 (segAdd machine _ _ _ 2 1
        (segAdd machine _ _ _ 1 1 hfirst hsecond) hthird) hfourth) hfifth) hsixth
  have hz : ∀ i : Nat, i<r → u (a+6+(i : Int))=false := by
    intro i hi
    have he : a+6+(i : Int)≠a+3 := by omega
    simpa [u,setAt,he] using zeros (a+6+(i : Int)) (by omega) (by omega)
  have hm : u (a+6+(r : Int))=true := by
    have he : a+6+(r : Int)≠a+3 := by omega
    simpa [u,setAt,he] using stop
  have hscan := scan10_return83 r (a+6) u hr hz hm
  have hall := segAdd machine _ _ _ 6 (r+2) hpref hscan
  simpa only [u,show 6+(r+2)=r+8 by omega] using hall

#print axioms terminal_marker_fill
end Shared.Beeping.NPcoNP.NativeTerminalMarkerFill
