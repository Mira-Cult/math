import Shared.Beeping.NPcoNP.NativeVariableZeroRoundtrip
import Shared.Beeping.NPcoNP.NativeVariableUnitRedispatch
import Shared.Beeping.NPcoNP.NativeShortPositiveWindow

/-! Derive the variable unit-increment inputs from a zero-selector layout. -/
namespace Shared.Beeping.NPcoNP.NativeVariableZeroToUnit
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
open Shared.Beeping.NPcoNP.NativeShortPositiveWindow
open Shared.Beeping.NPcoNP.NativeVariableWindowWords
open Shared.Beeping.NPcoNP.NativeVariableZeroRoundtrip
open Shared.Beeping.NPcoNP.NativeVariableUnitRedispatch
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- The supplied zero-stage control and bank yield all inputs for the next
unit increment, with the bank's extra zero block made explicit. -/
theorem variable_zero_to_unit (t : Int → Bool) (a : Int) (k s v : Nat)
    (rest : List Nat) (pad : List Bool) (hk : k≤10)
    (hpre : Holds t a (markerWindow (List.replicate k 0 ++ [0])))
    (blank : ∀ q, q<a-2 → t q=false)
    (left0 : t (a-2)=false) (left1 : t (a-1)=true)
    (mark : t (a+((2*k : Nat):Int)+2)=true)
    (corr : ∀ q, a+((2*k : Nat):Int)+2<q → q<a+((2*k : Nat):Int)+4+((s+6 : Nat):Int) → t q=false)
    (stop : t (a+((2*k : Nat):Int)+4+((s+6 : Nat):Int))=true)
    (delim : t (a+((2*k : Nat):Int)+4+((s+7 : Nat):Int))=false)
    (bank : Holds t (a+((2*k : Nat):Int)+4+((s+8 : Nat):Int))
      ((encode (v::rest) ++ [true,false,false]) ++ pad)) :
    let d := a+((2*k : Nat):Int)+4
    let out := fillRange (setAt d t) (d+2) (d+2+((s+4 : Nat):Int))
    silentSegment machine (cfg 93 a t) (cfg 93 a out) (2*k+2*s+46) ∧
      Holds out a (markerWindow (List.replicate k 0 ++ 1::0::(s+2)::[])) ∧
      Holds out (a-2) (zeroPairs (k+2)) ∧ (∀ q, q<a-2 → out q=false) ∧
      out (a+((2*k : Nat):Int)+2)=true ∧ out (a+((2*k : Nat):Int)+3)=false ∧
      out (a+((2*k : Nat):Int)+5)=false ∧
      Holds out (a+((2*k : Nat):Int)+6) (List.replicate (s+5) true ++ [false]) ∧
      Holds out (a+((2*k : Nat):Int)+4+((s+8 : Nat):Int))
        ((encode (v::(rest ++ [0])) ++ [false]) ++ pad) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let stopPos := d+((s+6 : Nat):Int)
  let x := d+((s+8 : Nat):Int)
  let out := fillRange (setAt d t) (d+2) (d+2+((s+4 : Nat):Int))
  have hnext : t (a+((2*k : Nat):Int)+3)=false := by apply corr <;> omega
  have h0 : t d=false := by apply corr <;> dsimp [d] <;> omega
  have h1 : t (d+1)=false := by apply corr <;> dsimp [d] <;> omega
  have hz : ∀ i : Nat, i<s+2+2 → t (a+((2*k : Nat):Int)+6+(i : Int))=false := by
    intro i hi
    apply corr <;> omega
  have hstop : t (a+((2*k : Nat):Int)+6+(((s+2)+2 : Nat):Int))=true := by
    have hp : a+((2*k : Nat):Int)+6+(((s+2)+2 : Nat):Int)=stopPos := by dsimp [stopPos,d]; push_cast; omega
    simpa only [hp,stopPos,d] using stop
  have hp1 : d+1=a+((2*k : Nat):Int)+5 := by dsimp [d]; omega
  obtain ⟨hseg,hwindow,hframe⟩ := variable_zero_roundtrip t a k (s+2) hk hpre blank left0 left1 mark hnext
    (by simpa only [d] using h0) (by simpa only [hp1] using h1) hz hstop
  have hseg' : silentSegment machine (cfg 93 a t) (cfg 93 a out) (2*k+2*s+46) := by
    have hc : 2*k+2*(s+2)+42=2*k+2*s+46 := by omega
    simpa only [d,out,hc,show s+2+2=s+4 by omega] using hseg
  have hf : ∀ q, q<d ∨ stopPos≤q → out q=t q := by
    have hp : d+2+(((s+2)+2 : Nat):Int)=stopPos := by dsimp [stopPos]; push_cast; omega
    simpa only [d,out,hp] using hframe
  have hfull : Holds out (a-2) (markerWindow (List.replicate (k+1) 0 ++ [1,0,s+2])) := by simpa only [d,out] using hwindow
  have hsplit : markerWindow (List.replicate (k+1) 0 ++ [1,0,s+2]) =
      [false,true] ++ markerWindow (List.replicate k 0 ++ [1,0,s+2]) := by
    have he : List.replicate (k+1) 0 ++ [1,0,s+2]=0::(List.replicate k 0 ++ [1,0,s+2]) := by simp [List.replicate_succ]
    rw [he,marker_zero_cons]
  have hunit : Holds out a (markerWindow (List.replicate k 0 ++ 1::0::(s+2)::[])) := by
    have hh := hfull
    rw [hsplit] at hh
    have ht := holds_append_tail out (a-2) [false,true] (markerWindow (List.replicate k 0 ++ [1,0,s+2])) hh
    have hp : a-2+(([false,true].length : Nat):Int)=a := by norm_num
    simpa only [hp] using ht
  have hpairs : Holds out (a-2) (zeroPairs (k+2)) := by
    have hh := hfull
    rw [variable_unit_window_word,zero_window_pairs] at hh
    have he : [false,true] ++ zeroPairs (k+1)=zeroPairs (k+2) := by
      change [false,true] ++ zeroPairs (k+1)=zeroPairs ((k+1)+1)
      rfl
    rw [he] at hh
    exact holds_prefix_word out (a-2) (zeroPairs (k+2)) _ (by simpa [List.append_assoc] using hh)
  have hblank : ∀ q, q<a-2 → out q=false := by
    intro q hq
    exact (hf q (Or.inl (by dsimp [d]; omega))).trans (blank q hq)
  have hmark : out (a+((2*k : Nat):Int)+2)=true := (hf _ (Or.inl (by dsimp [d]; omega))).trans mark
  have hzero0 : out (a+((2*k : Nat):Int)+3)=false := (hf _ (Or.inl (by dsimp [d]; omega))).trans hnext
  have hzero1 : out (a+((2*k : Nat):Int)+5)=false := by
    have hp : d+1=a+((2*k : Nat):Int)+5 := by dsimp [d]; omega
    have hh : out (d+1)=false := by simpa [out,fillRange,setAt] using h1
    simpa only [hp] using hh
  have hrun0 : Holds out (d+2) (List.replicate (s+4) true) := by
    apply holds_of_get
    intro i hi
    have hi' : i<s+4 := by simpa using hi
    have hr : d+2≤d+2+(i : Int) ∧ d+2+(i : Int)<d+2+((s+4 : Nat):Int) := by omega
    simp only [List.getElem_replicate]
    simp [out,fillRange,hr] <;> omega
  have houtstop : out stopPos=true := (hf _ (Or.inr (by omega))).trans (by simpa [stopPos,d] using stop)
  have houtdelim : out (stopPos+1)=false := (hf _ (Or.inr (by omega))).trans (by
    have hp : stopPos+1=a+((2*k : Nat):Int)+4+((s+7 : Nat):Int) := by dsimp [stopPos,d]; push_cast; omega
    simpa only [hp] using delim)
  have hpair : Holds out stopPos [true,false] := by
    simp only [Holds]
    exact ⟨houtstop,houtdelim,trivial⟩
  have hrun : Holds out (d+2) (List.replicate (s+5) true ++ [false]) := by
    have hh := holds_append_intro out (d+2) (List.replicate (s+4) true) [true,false] hrun0 (by
      have hp : d+2+((List.replicate (s+4) true).length : Int)=stopPos := by simp [stopPos]; push_cast; omega
      rw [hp]
      exact hpair)
    have he : List.replicate (s+4) true ++ [true,false]=List.replicate (s+5) true ++ [false] := by
      calc
        _ = (List.replicate (s+4) true ++ [true]) ++ [false] := by simp [List.append_assoc]
        _ = List.replicate ((s+4)+1) true ++ [false] := by
          have hhrep : List.replicate ((s+4)+1) true=List.replicate (s+4) true ++ [true] := List.replicate_succ'
          exact congrArg (fun xs => xs ++ [false]) hhrep.symm
        _ = _ := by congr 2 <;> omega
    simpa only [he] using hh
  have hbankword : encode (v::(rest ++ [0])) ++ [false] = encode (v::rest) ++ [true,false,false] := by
    have he : v::(rest ++ [0])=(v::rest) ++ [0] := by simp
    rw [he,append_zero_block]
    simp [List.append_assoc]
  have hbank : Holds out x ((encode (v::(rest ++ [0])) ++ [false]) ++ pad) := by
    rw [hbankword]
    apply holds_transport t out _ _ (by simpa only [x,d] using bank)
    intro q hq _
    exact (hf q (Or.inr (by dsimp [x,stopPos] at hq ⊢; omega))).symm
  have hrun' : Holds out (a+((2*k : Nat):Int)+6) (List.replicate (s+5) true ++ [false]) := by
    have hp : d+2=a+((2*k : Nat):Int)+6 := by dsimp [d]; omega
    simpa only [hp] using hrun
  exact ⟨hseg',hunit,hpairs,hblank,hmark,hzero0,hzero1,hrun',by simpa only [d,x] using hbank⟩

#print axioms variable_zero_to_unit
end Shared.Beeping.NPcoNP.NativeVariableZeroToUnit
