import Shared.Beeping.NPcoNP.NativePostAbsenceUnitScan
import Shared.Beeping.NPcoNP.NativeAllZeroAbsentExact
import Shared.Beeping.NPcoNP.NativeAllZeroReturnWindow
import Shared.Beeping.NPcoNP.NativeAllZeroSelector

/-! Parameterized state-261 round trip from the post-absence control layout.
This supplied-layout theorem does not assert global graph refinement. -/
namespace Shared.Beeping.NPcoNP.NativeFilledUnitWindow
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
open Shared.Beeping.NPcoNP.NativePostAbsenceUnitScan
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

/-! The filled unit window does not require a preceding marker. -/
theorem filled_unit_window (a : Int) (r : Nat) (t : Int → Bool)
    (hpre : Holds t a (zeroWord.take 24))
    (mark : t (a+24)=true)
    (corr : ∀ q, a+24<q → q<a+34+(r : Int) → t q=false) :
    Holds (scanOutput a r t) a (markerWindow (List.replicate 11 0 ++ [1,0,r+4])) := by
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
  have hs := next_window_split (r+2)
  have hrep : r+2+3=r+5 := by omega
  have hval : r+2+2=r+4 := by omega
  rw [hrep,hval] at hs
  rw [hs]
  simpa [List.append_assoc] using hfull

#print axioms filled_unit_window
end Shared.Beeping.NPcoNP.NativeFilledUnitWindow
