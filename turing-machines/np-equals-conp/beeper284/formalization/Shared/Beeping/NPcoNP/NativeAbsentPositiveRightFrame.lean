import Shared.Beeping.NPcoNP.NativeAllZeroUnitPositive
import Shared.Beeping.NPcoNP.NativeAllZeroUnitWindow
import Shared.Beeping.NPcoNP.NativePositiveSelectorControl
import Shared.Beeping.NPcoNP.NativeAbsentUnitScanRightFrame

/-! Compose the prepared unit scan with the generic positive selector.
This module does not assert blank-start reachability or graph refinement. -/
namespace Shared.Beeping.NPcoNP.NativeAbsentPositiveRightFrame
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroUnitScan
open Shared.Beeping.NPcoNP.NativeAllZeroUnitPositive
open Shared.Beeping.NPcoNP.NativeAbsentUnitScanRightFrame
open Shared.Beeping.NPcoNP.NativeAllZeroUnitWindow
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativePositiveSelectorControl
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000
attribute [local irreducible] machine

theorem padded_absent_next_positive_with_right_frame (a : Int) (r v : Nat) (rest : List Nat)
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
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      silentSegment machine (cfg 93 a t) (cfg 83 (a+23) out) n ∧
      out (a+24)=true ∧ out (a+35+(r : Int))=false ∧
      (∀ q, a+24<q → q<a+34+(r : Int) → out q=false) ∧
      out (a+34+(r : Int))=true ∧
      Holds out (a+36+(r : Int))
        ((encode (v::(rest ++ [0])) ++ [true,false,false]) ++ suffix) ∧
      (∀ q, q<a+24 → out q=t q) ∧
      (∀ q, a+36+(r : Int)+(((encode (v::rest) ++ [false,false,false]) ++ [false,false]).length : Int)≤q → out q=t q) := by
  obtain ⟨mid,e,n,hs,he,hn,hseg,hbank,h26,h29,h35,hframe,hunitright⟩ :=
    padded_absent_unit_scan_with_right_frame a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  let tape := fillRange (setAt (a+28) (carryOutput a r e.tape)) (a+30) (a+34+(r : Int))
  have hwindow := unit_scan_window a r t e.tape window h26 h29 hframe
  have hmarker : tape (a-1)=true := (hframe _ (by omega)).trans earlier
  have hlen : (encode (List.replicate 12 0 ++ [3,r+2])).length=r+33 := by
    simp [encode,block_length]
    omega
  have hext : Holds tape (a+((encode (List.replicate 12 0 ++ [3,r+2])).length : Int))
      (List.replicate 2 true ++ [false]) := by
    rw [hlen]
    have hp : a+((r+33 : Nat):Int)=a+33+(r : Int) := by push_cast; omega
    rw [hp]
    exact unit_scan_extension a r e.tape h35
  have hbank' : Holds tape (a+28+((r+2 : Nat):Int)+(2:Int)+4)
      (encode ((v+1)::(rest ++ [0])) ++ [false,false]) := by
    have hp : a+28+((r+2 : Nat):Int)+(2:Int)+4=a+36+(r : Int) := by push_cast; omega
    rw [hp]
    exact holds_prefix_word tape _ _ suffix hbank
  obtain ⟨m,out,hmpos,hmark,hblank,houtbank,hcorr,hstop,houtframe,hright,hnext⟩ :=
    terminal_positive_zero_control_with_right_frame tape a (r+2) 2 v (rest ++ [0]) hmarker hwindow hext hbank'
  have hstart : a+((encode (List.replicate 12 0 ++ [3,r+2])).length : Int)-1=a+32+(r : Int) := by
    rw [hlen]; push_cast; omega
  have hhead : a+((2*12 : Nat):Int)+4-5=a+23 := by norm_num; omega
  have hposmark : a+((2*12 : Nat):Int)+4-4=a+24 := by norm_num
  have hbankpos : a+((2*12 : Nat):Int)+4+(0:Int)+((r+2 : Nat):Int)+(2:Int)+4=a+36+(r : Int) := by
    norm_num; push_cast; omega
  rw [hstart,hhead] at hnext
  rw [hposmark] at hmark
  change out (a+((2*12 : Nat):Int)+4+(0:Int)+((r+2 : Nat):Int)+(2:Int)+4-1)=false at hblank
  change out (a+((2*12 : Nat):Int)+4+(0:Int)+((r+2 : Nat):Int)+(2:Int)+4-2)=true at hstop
  change Holds out (a+((2*12 : Nat):Int)+4+(0:Int)+((r+2 : Nat):Int)+(2:Int)+4) _ at houtbank
  rw [hbankpos] at hblank hstop houtbank
  have hflat (vs : List Nat) :
      (vs.flatMap (fun z => false :: List.replicate (z+1) true)).length = (encode vs).length := by
    induction vs with
    | nil => rfl
    | cons x xs ih => simp [encode,block,ih]; omega
  let vs := rest ++ [0]
  let inputWord := encode ((v+1)::vs) ++ [false,false]
  let outputWord := encode (v::vs) ++ [true,false,false]
  let z := a+36+(r : Int)
  let gap := (List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)).length
  have hlenwords : inputWord.length=outputWord.length := by
    simp [inputWord,outputWord,encode,block]
    omega
  have hgap : inputWord.length=gap+5 := by
    simp [inputWord,gap,encode,block,hflat]
    omega
  have htail : Holds tape (z+(inputWord.length : Int)) suffix :=
    holds_append_tail tape z inputWord suffix hbank
  have htail' : Holds out (z+(inputWord.length : Int)) suffix := by
    apply holds_transport tape out _ _ htail
    intro q hq _
    symm
    apply hright q
    change a+((2*12 : Nat):Int)+4+(0:Int)+((r+2 : Nat):Int)+(2:Int)+4+2+(gap : Int)<q
    rw [hbankpos]
    change z+2+(gap : Int)<q
    rw [hgap] at hq
    push_cast at hq
    omega
  have houtbank' : Holds out z (outputWord ++ suffix) := by
    apply holds_append_intro out z outputWord suffix houtbank
    rw [← hlenwords]
    exact htail'
  have hOriginalLen : ((encode (v::rest) ++ [false,false,false]) ++ [false,false]).length=inputWord.length := by
    simp [inputWord,vs,encode_append,encode,block_length]
    omega
  have hall := segAdd machine _ _ _ n m hseg hnext
  refine ⟨n+m,out,by omega,hall,hmark,?_,?_,?_,houtbank',?_,?_⟩
  · simpa only [show a+36+(r : Int)-1=a+35+(r : Int) by omega] using hblank
  · intro q hq hq'
    apply hcorr q <;> norm_num <;> omega
  · simpa only [show a+36+(r : Int)-2=a+34+(r : Int) by omega] using hstop
  · intro q hq
    calc
      out q=tape q := houtframe q (by norm_num; omega)
      _=t q := hframe q (by omega)
  · intro q hq
    have hq' : z+((inputWord.length : Nat):Int)≤q := by
      dsimp [z]
      simpa only [hOriginalLen] using hq
    have hf : a+((2*12 : Nat):Int)+4+(0:Int)+((r+2 : Nat):Int)+(2:Int)+4+2+(gap : Int)<q := by
      rw [hbankpos]
      change z+2+(gap : Int)<q
      rw [hgap] at hq'
      push_cast at hq'
      omega
    calc
      out q=tape q := hright q hf
      _=t q := hunitright q hq


#print axioms padded_absent_next_positive_with_right_frame
end Shared.Beeping.NPcoNP.NativeAbsentPositiveRightFrame
