import Shared.Beeping.NPcoNP.NativeState260Scanner
import Shared.Beeping.NPcoNP.NativeAllZeroUnitScan
import Shared.Beeping.NPcoNP.NativeAbsentIncrementRightFrame

/-! Derive the state-260 scanner corridor from the preceding near carry.
All results assume supplied tape layouts and finite segments. -/
namespace Shared.Beeping.NPcoNP.NativeAbsentUnitScanRightFrame
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeAllZeroNearCarry
open Shared.Beeping.NPcoNP.NativeAllZeroNextReturn
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeState260Scanner
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroUnitScan
open Shared.Beeping.NPcoNP.NativeAbsentIncrementRightFrame
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

theorem padded_absent_unit_scan_with_right_frame (a : Int) (r v : Nat) (rest : List Nat)
    (suffix : List Bool) (t : Int → Bool)
    (window : Holds t a zeroWord)
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
    (absent : t (a-3)=false)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int))
      ((encode (v::rest) ++ [false,false,false]) ++ ([false,false] ++ suffix))) :
    ∃ (mid e : Config 284) (n : Nat), mid.state=23 ∧ e.state=23 ∧ 0<n ∧
      let output := fillRange (setAt (a+28) (carryOutput a r e.tape))
        (a+30) (a+34+(r : Int))
      silentSegment machine (cfg 93 a t) (cfg 83 (a+32+(r : Int)) output) n ∧
      Holds output (a+36+(r : Int))
        ((encode ((v+1)::(rest ++ [0])) ++ [false,false]) ++ suffix) ∧
      e.tape (a+26)=true ∧ e.tape (a+29)=false ∧
      e.tape (a+35+(r : Int))=false ∧
      (∀ q, q<a+26 → output q=t q) ∧
      (∀ q, a+36+(r : Int)+(((encode (v::rest) ++ [false,false,false]) ++ [false,false]).length : Int)≤q → output q=t q) := by
  obtain ⟨mid,e,hs,he,hseg,hbank,_hmissing,hleft,h27,h28,h29,hrun,h26⟩ :=
    padded_absent_increment_return1_with_marker a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  have hcore : Holds t (a+36+(r : Int)) ((encode (v::rest) ++ [false,false,false]) ++ [false,false]) := by
    apply holds_prefix_word t _ _ suffix
    simpa only [List.append_assoc] using bank
  have hright := return1_right_frame a r v rest t window left0 earlier absent marker nextZero h0 h1 hz hm delimiter
    hcore e (by simpa only [duration] using hseg)
  let carried := carryOutput a r e.tape
  let output := fillRange (setAt (a+28) carried) (a+30) (a+34+(r : Int))
  have hframe : ∀ q, q<a+26 → carried q=t q := by
    intro q hq
    calc
      carried q=e.tape q := near_carry_frame a r e.tape q (Or.inl (by omega))
      _=t q := hleft q hq
  have hmark : carried (a+26)=true := by
    have hf : carried (a+26)=e.tape (a+26) := near_carry_frame a r e.tape (a+26) (Or.inl (by omega))
    exact hf.trans h26
  have hwindow := unit_window_of_frame a t carried window left0 earlier hframe hmark
  have habsent : carried (a-3)=false := (hframe _ (by omega)).trans absent
  have hnext := near_carry_unit_scan a r e.tape h27 h28 h29 hrun hwindow habsent
  have hall := segAdd machine _ _ _ _ ((2*r+17)+(60+(r+8))) hseg hnext
  have hbank' : Holds output (a+36+(r : Int))
      ((encode ((v+1)::(rest ++ [0])) ++ [false,false]) ++ suffix) := by
    apply holds_transport e.tape output _ _ hbank
    intro q hq _
    symm
    calc
      output q=carried q := by
        have hf := dispatch260_frame (r+4) (a+28) carried q (Or.inr (by push_cast; omega))
        have hstart : a+28+2=a+30 := by omega
        have hend : a+30+((r+4 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
        simpa only [hstart,hend,output] using hf
      _=e.tape q := near_carry_frame a r e.tape q (Or.inr (by omega))
  have hleft' : ∀ q, q<a+26 → output q=t q := by
    intro q hq
    calc
      output q=carried q := by
        have hf := dispatch260_frame (r+4) (a+28) carried q (Or.inl (by omega))
        have hstart : a+28+2=a+30 := by omega
        have hend : a+30+((r+4 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
        simpa only [hstart,hend,output] using hf
      _=t q := hframe q hq
  have hstop := (split_ones (r+5) (a+30) e.tape [false] hrun).2
  have h35 : e.tape (a+35+(r : Int))=false := by
    have hp : a+30+((r+5 : Nat):Int)=a+35+(r : Int) := by push_cast; omega
    simp only [Holds,and_true] at hstop
    rw [hp] at hstop
    exact hstop
  refine ⟨mid,e,_,hs,he,?_,hall,hbank',h26,h29,h35,hleft',?_⟩
  · omega
  · intro q hq
    have hp : a+36+(r : Int)≤q := by omega
    calc
      output q=carried q := by
        have hf := dispatch260_frame (r+4) (a+28) carried q (Or.inr (by push_cast; omega))
        have hstart : a+28+2=a+30 := by omega
        have hend : a+30+((r+4 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
        simpa only [hstart,hend,output] using hf
      _=e.tape q := near_carry_frame a r e.tape q (Or.inr (by omega))
      _=t q := hright q hq


#print axioms padded_absent_unit_scan_with_right_frame
end Shared.Beeping.NPcoNP.NativeAbsentUnitScanRightFrame
