import Shared.Beeping.NPcoNP.NativePostIncrementPositiveScan
import Shared.Beeping.NPcoNP.NativeAllZeroUnitWindow
import Shared.Beeping.NPcoNP.NativeTerminalUnitSelector

/-! State-260 round trip after the post-absence increment. The hypotheses
describe a supplied finite control layout, not global graph refinement. -/
namespace Shared.Beeping.NPcoNP.NativeShortPositiveWindow
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeAllZeroUnitWindow
open Shared.Beeping.NPcoNP.NativeAllZeroReturnWindow
open Shared.Beeping.NPcoNP.NativePostAbsenceUnitScan
open Shared.Beeping.NPcoNP.NativeTerminalUnitSelector
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000
attribute [local irreducible] machine

theorem marker_zero_cons (xs : List Nat) :
    markerWindow (0::xs)=[false,true] ++ markerWindow xs := by
  apply List.append_cancel_right (bs := [false])
  simp only [List.append_assoc,markerWindow_append_zero,encode,block,List.replicate_succ,
    List.replicate_zero,List.cons_append,List.nil_append]

theorem short_positive_window (a : Int) (r : Nat) (t : Int → Bool)
    (hpre : Holds t a (zeroWord.take 24))
    (h24 : t (a+24)=true) (h25 : t (a+25)=true)
    (corr : ∀ q, a+25<q → q<a+34+(r : Int) → t q=false) :
    Holds (scanOutput a r t) a (markerWindow (List.replicate 11 0 ++ [3,r+4])) := by
  let out := scanOutput a r t
  have hprefixeq : zeroWord.take 24=preservedPrefix := by decide
  have hprefix : Holds out a preservedPrefix := by
    apply holds_transport t out _ _ (by simpa only [hprefixeq] using hpre)
    intro q _ hq
    have hl : preservedPrefix.length=24 := by decide
    rw [hl] at hq
    exact (scan_output_frame a r t q (Or.inl (by omega))).symm
  have h24' : out (a+24)=true := (scan_output_frame a r t _ (Or.inl (by omega))).trans h24
  have h25' : out (a+25)=true := (scan_output_frame a r t _ (Or.inl (by omega))).trans h25
  have h26' : out (a+26)=true := by simp [out,scanOutput,fillRange,setAt]
  have h27' : out (a+27)=false := by
    have hz := corr (a+27) (by omega) (by omega)
    simpa [out,scanOutput,fillRange,setAt] using hz
  have hrun : Holds out (a+28) (List.replicate (r+5) true) := by
    apply holds_of_get
    intro i hi
    have hi' : i<r+5 := by simpa using hi
    have hp : a+28≤a+28+(i : Int) ∧ a+28+(i : Int)<a+34+(r : Int) := by omega
    simp [out,scanOutput,fillRange,hp]
  have htail : Holds out (a+24) ([true,true,true,false] ++ List.replicate (r+5) true) := by
    simp only [List.cons_append,List.nil_append,Holds]
    refine ⟨h24',?_,?_,?_,?_⟩
    · simpa only [show a+24+1=a+25 by omega] using h25'
    · simpa only [show a+24+1+1=a+26 by omega] using h26'
    · simpa only [show a+24+1+1+1=a+27 by omega] using h27'
    · simpa only [show a+24+1+1+1+1=a+28 by omega] using hrun
  have hfull := holds_append_intro out a preservedPrefix
    ([true,true,true,false] ++ List.replicate (r+5) true) hprefix (by
      have hl : preservedPrefix.length=24 := by decide
      have hp : a+((preservedPrefix.length : Nat):Int)=a+24 := by rw [hl]; norm_num
      rw [hp]
      exact htail)
  have hs := unit_scan_window_split (r+2)
  have hrep : r+2+3=r+5 := by omega
  have hval : r+2+2=r+4 := by omega
  rw [hrep,hval] at hs
  have hcons : markerWindow (List.replicate 12 0 ++ [3,r+4]) =
      [false,true] ++ markerWindow (List.replicate 11 0 ++ [3,r+4]) := by
    have he : List.replicate 12 0 ++ [3,r+4] = 0::(List.replicate 11 0 ++ [3,r+4]) := by rfl
    rw [he,marker_zero_cons]
  rw [hcons] at hs
  have hs' : markerWindow (List.replicate 11 0 ++ [3,r+4]) =
      preservedPrefix ++ ([true,true,true,false] ++ List.replicate (r+5) true) := by
    apply List.append_cancel_left (as := [false,true])
    simpa [List.append_assoc] using hs
  rw [hs']
  simpa [List.append_assoc] using hfull

#print axioms short_positive_window
end Shared.Beeping.NPcoNP.NativeShortPositiveWindow
