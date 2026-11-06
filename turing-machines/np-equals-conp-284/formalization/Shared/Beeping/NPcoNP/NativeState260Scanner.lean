import Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
import Shared.Beeping.NPcoNP.NativeHalfMarkerTwoSafe
import Shared.Beeping.NPcoNP.NativeHalfScannerReturns

/-! Exact, finite state-260 scanner segments for supplied tapes. These lemmas
do not assert that their hypotheses hold on the blank-start execution. -/
namespace Shared.Beeping.NPcoNP.NativeState260Scanner

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfMarkerTwoSafe
open Shared.Beeping.NPcoNP.NativeHalfScannerReturns
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

set_option autoImplicit false
set_option maxRecDepth 8192
attribute [local irreducible] machine

/-- Both state 260 and state 261 have the same silent transition on zero.
The following zero moves state 42 to the state-10 scanner; a nonempty zero
run is filled, and the next marker returns the head to state 83. -/
theorem dispatch260_return83_exact (k : Nat) (h : Int) (t : Int → Bool)
    (hk : 0<k) (h0 : t h=false) (h1 : t (h+1)=false)
    (hz : ∀ i : Nat, i<k → t (h+2+(i : Int))=false)
    (hm : t (h+2+(k : Int))=true) :
    silentSegment machine (cfg 260 h t)
      (cfg 83 (h+(k : Int)) (fillRange (setAt h t) (h+2) (h+2+(k : Int)))) (k+4) := by
  let t1 := setAt h t
  have h1' : t1 (h+1)=false := by simp [t1,setAt,h1,show h+1≠h by omega]
  have hz' : ∀ i : Nat, i<k → t1 (h+2+(i : Int))=false := by
    intro i hi
    change (if h+2+(i : Int)=h then true else t (h+2+(i : Int)))=false
    rw [if_neg (by omega)]
    exact hz i hi
  have hm' : t1 (h+2+(k : Int))=true := by
    change (if h+2+(k : Int)=h then true else t (h+2+(k : Int)))=true
    rw [if_neg (by omega)]
    exact hm
  have hfirst := oneSeg machine _ _ (step260_zero h t h0)
  have hsecond := oneSeg machine _ _ (step42_zero (h+1) t1 h1')
  have hprefix : silentSegment machine (cfg 260 h t) (cfg 10 (h+2) t1) 2 := by
    have hseg := segAdd machine _ _ _ 1 1 hfirst hsecond
    have he : h+1+1=h+2 := by omega
    simpa only [he] using hseg
  have hscan := scan10_return83 k (h+2) t1 hk hz' hm'
  have hall := segAdd machine _ _ _ 2 (k+2) hprefix hscan
  have hp : h+2+(k : Int)-2=h+(k : Int) := by omega
  have hn : 2+(k+2)=k+4 := by omega
  simpa only [hp,hn,t1] using hall

/-- The scanner changes only its entry cell and the scanned zero interval. -/
theorem dispatch260_frame (k : Nat) (h : Int) (t : Int → Bool) (q : Int)
    (hq : q<h ∨ h+2+(k : Int)≤q) :
    fillRange (setAt h t) (h+2) (h+2+(k : Int)) q=t q := by
  have hn : q≠h := by omega
  have hr : ¬ (h+2≤q ∧ q<h+2+(k : Int)) := by omega
  simp [fillRange,setAt,hn,hr]

/-- A supplied unit selector with an absent earlier marker can be followed
through the state-260 scanner, with the complete output tape and cost. -/
theorem unit_absent_scanner_return (a : Int) (k : Nat) (t : Int → Bool)
    (window : Holds t (a-2) unitWord) (absent : t (a-3)=false)
    (marker : t (a+27)=true) (nextZero : t (a+28)=false)
    (hk : 0<k) (after : t (a+29)=false)
    (hz : ∀ i : Nat, i<k → t (a+30+(i : Int))=false)
    (hm : t (a+30+(k : Int))=true) :
    silentSegment machine (cfg 83 (a+26) t)
      (cfg 83 (a+28+(k : Int))
        (fillRange (setAt (a+28) t) (a+30) (a+30+(k : Int)))) (60+(k+4)) := by
  have hfirst := unit_absent_to260 a t window absent marker nextZero
  have hsecond := dispatch260_return83_exact k (a+28) t hk nextZero
    (by simpa only [show a+28+1=a+29 by omega] using after)
    (by simpa only [show a+28+2=a+30 by omega] using hz)
    (by simpa only [show a+28+2=a+30 by omega] using hm)
  have hall := segAdd machine _ _ _ 60 (k+4) hfirst hsecond
  simpa only [show a+28+2=a+30 by omega] using hall

#print axioms dispatch260_return83_exact
#print axioms dispatch260_frame
#print axioms unit_absent_scanner_return
end Shared.Beeping.NPcoNP.NativeState260Scanner
