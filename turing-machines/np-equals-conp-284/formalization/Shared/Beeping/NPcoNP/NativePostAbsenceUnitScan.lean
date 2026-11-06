import Shared.Beeping.NPcoNP.NativeAllZeroPositiveDispatch
import Shared.Beeping.NPcoNP.NativeAllZeroAbsentExact
import Shared.Beeping.NPcoNP.NativeAllZeroReturnWindow
import Shared.Beeping.NPcoNP.NativeAllZeroSelector

/-! Parameterized state-261 round trip from the post-absence control layout.
This supplied-layout theorem does not assert global graph refinement. -/
namespace Shared.Beeping.NPcoNP.NativePostAbsenceUnitScan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroSelector
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentExact
open Shared.Beeping.NPcoNP.NativeAllZeroReturnWindow
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000
attribute [local irreducible] machine

def scanOutput (a : Int) (r : Nat) (t : Int → Bool) : Int → Bool :=
  fillRange (setAt (a+26) t) (a+28) (a+34+(r : Int))

theorem prefix_word : zeroWord.take 24=markerWindow (List.replicate 11 0 ++ [0]) := by decide

/-- The supplied post-absence control enters state 261 and fills its zero
corridor in exactly `r+36` silent transitions. -/
theorem post_absence_to83 (a : Int) (r : Nat) (t : Int → Bool)
    (hpre : Holds t a (zeroWord.take 24)) (mark : t (a+24)=true)
    (corr : ∀ q, a+24<q → q<a+34+(r : Int) → t q=false)
    (stop : t (a+34+(r : Int))=true) :
    silentSegment machine (cfg 93 a t) (cfg 83 (a+32+(r : Int)) (scanOutput a r t)) (r+36) := by
  have hp : Holds t a (markerWindow (List.replicate 11 0 ++ [0])) := by simpa only [prefix_word] using hpre
  have hnext : t (a+((2*11 : Nat):Int)+3)=false := by
    have he : a+((2*11 : Nat):Int)+3=a+25 := by norm_num; omega
    rw [he]
    exact corr _ (by omega) (by omega)
  have hmark : t (a+((2*11 : Nat):Int)+2)=true := by
    have he : a+((2*11 : Nat):Int)+2=a+24 := by norm_num; omega
    simpa only [he] using mark
  have hdispatch := all_zero_to261 t a 11 hp hmark hnext
  have hdispatch' : silentSegment machine (cfg 93 a t) (cfg 261 (a+26) t) 26 := by
    have he : a+((2*11 : Nat):Int)+4=a+26 := by norm_num; omega
    simpa only [he,show 2*11+4=26 by decide] using hdispatch
  have h0 : t (a+26)=false := corr _ (by omega) (by omega)
  have h1 : t (a+26+1)=false := corr _ (by omega) (by omega)
  have hz : ∀ i : Nat, i<r+6 → t (a+26+2+(i : Int))=false := by
    intro i hi
    apply corr <;> omega
  have hm : t (a+26+2+((r+6 : Nat):Int))=true := by
    have he : a+26+2+((r+6 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
    simpa only [he] using stop
  have hreturn := dispatch261_return83_exact (r+6) (a+26) t (by omega) h0 h1 hz hm
  have hreturn' : silentSegment machine (cfg 261 (a+26) t)
      (cfg 83 (a+32+(r : Int)) (scanOutput a r t)) (r+10) := by
    have hhead : a+26+((r+6 : Nat):Int)=a+32+(r : Int) := by push_cast; omega
    have hend : a+26+2+((r+6 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
    have hstart : a+26+2=a+28 := by omega
    have hend' : a+28+((r+6 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
    have hcost : r+6+4=r+10 := by omega
    simpa only [hhead,hend,hstart,hend',hcost,scanOutput] using hreturn
  have hall := segAdd machine _ _ _ 26 (r+10) hdispatch' hreturn'
  have hc : 26+(r+10)=r+36 := by omega
  simpa only [hc] using hall

/-- The filled scan changes only its entry cell and its zero corridor. -/
theorem scan_output_frame (a : Int) (r : Nat) (t : Int → Bool) (q : Int)
    (hq : q<a+26 ∨ a+34+(r : Int)≤q) : scanOutput a r t q=t q := by
  have hn : q≠a+26 := by omega
  have hr : ¬ (a+28≤q ∧ q<a+34+(r : Int)) := by omega
  simp [scanOutput,fillRange,setAt,hn,hr]

/-- The filled tape is a new marked selector, with the expected three
trailing values and the earlier marker still present. -/
theorem post_absence_next_window (a : Int) (r : Nat) (t : Int → Bool)
    (hpre : Holds t a (zeroWord.take 24)) (left : t (a-1)=true)
    (mark : t (a+24)=true)
    (corr : ∀ q, a+24<q → q<a+34+(r : Int) → t q=false) :
    Holds (scanOutput a r t) a (markerWindow (List.replicate 11 0 ++ [1,0,r+4])) ∧
      scanOutput a r t (a-1)=true := by
  let out := scanOutput a r t
  have heq : zeroWord.take 24=preservedPrefix := by decide
  have hprefix : Holds out a preservedPrefix := by
    apply holds_transport t out _ _ (by simpa only [heq] using hpre)
    intro q _ hq
    have hl : preservedPrefix.length=24 := by decide
    rw [hl] at hq
    exact (scan_output_frame a r t q (Or.inl (by omega))).symm
  have h24 : out (a+24)=true := (scan_output_frame a r t _ (Or.inl (by omega))).trans mark
  have h25 : out (a+25)=false := (scan_output_frame a r t _ (Or.inl (by omega))).trans (corr _ (by omega) (by omega))
  have h26 : out (a+26)=true := by simp [out,scanOutput,fillRange,setAt]
  have h27 : out (a+27)=false := by
    have ht : t (a+27)=false := corr _ (by omega) (by omega)
    simpa [out,scanOutput,fillRange,setAt] using ht
  have hrun : Holds out (a+28) (List.replicate (r+5) true) := by
    apply holds_of_get
    intro i hi
    have hi' : i<r+5 := by simpa using hi
    have hp : a+28≤a+28+(i : Int) ∧ a+28+(i : Int)<a+34+(r : Int) := by omega
    simp [out,scanOutput,fillRange,hp]
  have htail : Holds out (a+24) ([true,false,true,false] ++ List.replicate (r+5) true) := by
    simp only [List.cons_append,List.nil_append,Holds]
    refine ⟨h24,?_,?_,?_,?_⟩
    · simpa only [show a+24+1=a+25 by omega] using h25
    · simpa only [show a+24+1+1=a+26 by omega] using h26
    · simpa only [show a+24+1+1+1=a+27 by omega] using h27
    · simpa only [show a+24+1+1+1+1=a+28 by omega] using hrun
  have hfull := holds_append_intro out a preservedPrefix
    ([true,false,true,false] ++ List.replicate (r+5) true) hprefix (by
      have hl : preservedPrefix.length=24 := by decide
      have hp : a+(preservedPrefix.length : Int)=a+24 := by rw [hl]; norm_num
      rw [hp]
      exact htail)
  constructor
  · have hs := next_window_split (r+2)
    have hrep : r+2+3=r+5 := by omega
    have hval : r+2+2=r+4 := by omega
    rw [hrep,hval] at hs
    rw [hs]
    simpa [List.append_assoc] using hfull
  · exact (scan_output_frame a r t _ (Or.inl (by omega))).trans left

/-- Return to state 93 at the same anchor after the post-absence unit scan;
the bank and arbitrary tape outside the written corridor are unchanged. -/
theorem post_absence_roundtrip (a : Int) (r : Nat) (t : Int → Bool)
    (hpre : Holds t a (zeroWord.take 24)) (left : t (a-1)=true)
    (mark : t (a+24)=true)
    (corr : ∀ q, a+24<q → q<a+34+(r : Int) → t q=false)
    (stop : t (a+34+(r : Int))=true) :
    silentSegment machine (cfg 93 a t) (cfg 93 a (scanOutput a r t)) (2*r+70) ∧
      Holds (scanOutput a r t) a (markerWindow (List.replicate 11 0 ++ [1,0,r+4])) ∧
      (∀ q, q<a+26 ∨ a+34+(r : Int)≤q → scanOutput a r t q=t q) := by
  have hfirst := post_absence_to83 a r t hpre mark corr stop
  obtain ⟨hw,hm⟩ := post_absence_next_window a r t hpre left mark corr
  have hnext := long_return_window_to93 (a-2) (r+2) (scanOutput a r t)
    (by simpa using hw) (by simpa only [show a-2+1=a-1 by omega] using hm)
  have hnext' : silentSegment machine (cfg 83 (a+32+(r : Int)) (scanOutput a r t))
      (cfg 93 a (scanOutput a r t)) (r+34) := by
    have hh : (a-2)+32+((r+2 : Nat):Int)=a+32+(r : Int) := by push_cast; omega
    have he : a-2+2=a := by omega
    have hc : r+2+32=r+34 := by omega
    simpa only [hh,he,hc] using hnext
  have hall := segAdd machine _ _ _ (r+36) (r+34) hfirst hnext'
  have hc : r+36+(r+34)=2*r+70 := by omega
  exact ⟨by simpa only [hc] using hall,hw,scan_output_frame a r t⟩

#print axioms post_absence_to83
#print axioms scan_output_frame
#print axioms post_absence_next_window
#print axioms post_absence_roundtrip
end Shared.Beeping.NPcoNP.NativePostAbsenceUnitScan
