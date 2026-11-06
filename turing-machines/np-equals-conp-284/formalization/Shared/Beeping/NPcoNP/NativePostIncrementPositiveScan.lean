import Shared.Beeping.NPcoNP.NativePostAbsenceIncrement
import Shared.Beeping.NPcoNP.NativeAllZeroUnitWindow
import Shared.Beeping.NPcoNP.NativeTerminalUnitSelector

/-! State-260 round trip after the post-absence increment. The hypotheses
describe a supplied finite control layout, not global graph refinement. -/
namespace Shared.Beeping.NPcoNP.NativePostIncrementPositiveScan
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

theorem short_unit_word : zeroWord.take 24 ++ [true]=markerWindow (List.replicate 11 0 ++ [1]) := by decide

/-- The incremented control selects state 260 and returns through the
supplied zero corridor in exactly `r+36` silent transitions. -/
theorem post_increment_to83 (a : Int) (r : Nat) (t : Int → Bool)
    (hpre : Holds t a (zeroWord.take 24)) (h24 : t (a+24)=true) (h25 : t (a+25)=true)
    (corr : ∀ q, a+25<q → q<a+34+(r : Int) → t q=false)
    (stop : t (a+34+(r : Int))=true) :
    silentSegment machine (cfg 93 a t) (cfg 83 (a+32+(r : Int)) (scanOutput a r t)) (r+36) := by
  have hlast : Holds t (a+24) [true] := by simpa [Holds] using h24
  have hw := holds_append_intro t a (zeroWord.take 24) [true] hpre (by
    have hl : (zeroWord.take 24).length=24 := by decide
    have hp : a+((zeroWord.take 24).length : Int)=a+24 := by rw [hl]; norm_num
    rw [hp]
    exact hlast)
  rw [short_unit_word] at hw
  have hz : ∀ i : Nat, i<r+6 → t (a+((2*11 : Nat):Int)+6+(i : Int))=false := by
    intro i hi
    apply corr <;> norm_num <;> omega
  have hstop : t (a+((2*11 : Nat):Int)+6+((r+6 : Nat):Int))=true := by
    have hp : a+((2*11 : Nat):Int)+6+((r+6 : Nat):Int)=a+34+(r : Int) := by norm_num; push_cast; omega
    simpa only [hp] using stop
  have h := terminal_unit_fill_return t a 11 (r+6) (by omega) hw
    (by
      have hp : a+((2*11 : Nat):Int)+3=a+25 := by norm_num; omega
      simpa only [hp] using h25)
    (by apply corr <;> norm_num <;> omega)
    (by apply corr <;> norm_num <;> omega) hz hstop
  have hd : a+((2*11 : Nat):Int)+4=a+26 := by norm_num; omega
  have hh : a+((2*11 : Nat):Int)+4+((r+6 : Nat):Int)=a+32+(r : Int) := by norm_num; push_cast; omega
  have hh' : a+26+((r+6 : Nat):Int)=a+32+(r : Int) := by push_cast; omega
  have hs : a+26+2=a+28 := by omega
  have he : a+28+((r+6 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
  have hc : 2*11+(r+6)+8=r+36 := by omega
  simpa only [hd,hh,hh',hs,he,hc,scanOutput] using h

/-- The filled tape has a fourteen-block window beginning two cells left
of the old anchor, even though the earlier marker remains absent. -/
theorem post_increment_next_window (a : Int) (r : Nat) (t : Int → Bool)
    (hpre : Holds t a (zeroWord.take 24)) (left0 : t (a-2)=false) (left : t (a-1)=true)
    (h24 : t (a+24)=true) (h25 : t (a+25)=true)
    (corr : ∀ q, a+25<q → q<a+34+(r : Int) → t q=false) :
    Holds (scanOutput a r t) (a-2) (markerWindow (List.replicate 12 0 ++ [3,r+4])) := by
  let out := scanOutput a r t
  have hprefixeq : zeroWord.take 24=preservedPrefix := by decide
  have hprefix : Holds out a preservedPrefix := by
    apply holds_transport t out _ _ (by simpa only [hprefixeq] using hpre)
    intro q _ hq
    have hl : preservedPrefix.length=24 := by decide
    rw [hl] at hq
    exact (scan_output_frame a r t q (Or.inl (by omega))).symm
  have hpair : Holds out (a-2) [false,true] := by
    simp only [Holds]
    exact ⟨(scan_output_frame a r t _ (Or.inl (by omega))).trans left0,
      by simpa only [show a-2+1=a-1 by omega] using
        (scan_output_frame a r t (a-1) (Or.inl (by omega))).trans left,trivial⟩
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
  have hprefix' := holds_append_intro out (a-2) [false,true] preservedPrefix hpair (by
    have hp : a-2+(([false,true].length : Nat):Int)=a := by norm_num
    rw [hp]
    exact hprefix)
  have hfull := holds_append_intro out (a-2) ([false,true] ++ preservedPrefix)
    ([true,true,true,false] ++ List.replicate (r+5) true) hprefix' (by
      have hl : ([false,true] ++ preservedPrefix).length=26 := by decide
      have hp : a-2+((([false,true] ++ preservedPrefix).length : Nat):Int)=a+24 := by rw [hl]; norm_num; omega
      rw [hp]
      exact htail)
  have hs := unit_scan_window_split (r+2)
  have hrep : r+2+3=r+5 := by omega
  have hval : r+2+2=r+4 := by omega
  rw [hrep,hval] at hs
  rw [hs]
  simpa [List.append_assoc] using hfull

/-- With the absent earlier marker, the state-260 path returns to the same
state-93 anchor, leaving the bank and all cells outside the scan untouched. -/
theorem post_increment_roundtrip (a : Int) (r : Nat) (t : Int → Bool)
    (hpre : Holds t a (zeroWord.take 24)) (left0 : t (a-2)=false) (left : t (a-1)=true)
    (absent : t (a-3)=false) (h24 : t (a+24)=true) (h25 : t (a+25)=true)
    (corr : ∀ q, a+25<q → q<a+34+(r : Int) → t q=false)
    (stop : t (a+34+(r : Int))=true) :
    silentSegment machine (cfg 93 a t) (cfg 93 a (scanOutput a r t)) (2*r+74) ∧
      Holds (scanOutput a r t) (a-2) (markerWindow (List.replicate 12 0 ++ [3,r+4])) ∧
      (∀ q, q<a+26 ∨ a+34+(r : Int)≤q → scanOutput a r t q=t q) := by
  have hfirst := post_increment_to83 a r t hpre h24 h25 corr stop
  have hw := post_increment_next_window a r t hpre left0 left h24 h25 corr
  let xs := List.replicate 12 0 ++ [3,r+4]
  have hl : (encode xs).length=r+35 := by simp [xs,encode,block_length]; omega
  have hscan := marker_window_to92 (scanOutput a r t) (a-2) xs (by simp [xs]) hw
  rw [hl] at hscan
  have hh : a-2+((r+35 : Nat):Int)-1=a+32+(r : Int) := by push_cast; omega
  have he : a-2-1=a-3 := by omega
  rw [hh,he] at hscan
  have hz3 : scanOutput a r t (a-3)=false := (scan_output_frame a r t _ (Or.inl (by omega))).trans absent
  have hz2 : scanOutput a r t (a-2)=false := (scan_output_frame a r t _ (Or.inl (by omega))).trans left0
  have ho1 : scanOutput a r t (a-1)=true := (scan_output_frame a r t _ (Or.inl (by omega))).trans left
  have h1 : silentSegment machine (cfg 92 (a-3) (scanOutput a r t)) (cfg 92 (a-2) (scanOutput a r t)) 1 := by
    simpa only [show a-3+1=a-2 by omega] using oneSeg machine _ _ (step92_zero (a-3) _ hz3)
  have h2 : silentSegment machine (cfg 92 (a-2) (scanOutput a r t)) (cfg 92 (a-1) (scanOutput a r t)) 1 := by
    simpa only [show a-2+1=a-1 by omega] using oneSeg machine _ _ (step92_zero (a-2) _ hz2)
  have h3 : silentSegment machine (cfg 92 (a-1) (scanOutput a r t)) (cfg 93 a (scanOutput a r t)) 1 := by
    simpa only [show a-1+1=a by omega] using oneSeg machine _ _ (step92_one (a-1) _ ho1)
  have h12 := segAdd machine _ _ _ 1 1 h1 h2
  have h123 := segAdd machine _ _ _ 2 1 h12 h3
  have hback := segAdd machine _ _ _ (r+35) 3 hscan h123
  have hall := segAdd machine _ _ _ (r+36) (r+35+3) hfirst hback
  have hc : r+36+(r+35+3)=2*r+74 := by omega
  exact ⟨by simpa only [hc] using hall,hw,scan_output_frame a r t⟩

#print axioms post_increment_to83
#print axioms post_increment_next_window
#print axioms post_increment_roundtrip
end Shared.Beeping.NPcoNP.NativePostIncrementPositiveScan
