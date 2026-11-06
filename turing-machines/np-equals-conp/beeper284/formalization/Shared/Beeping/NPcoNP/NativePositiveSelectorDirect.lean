import Shared.Beeping.NPcoNP.NativePositiveSelectorControl
import Shared.Beeping.NPcoNP.NativeManyTerminalPositiveMarker

/-! Connect the zero-index positive selector to its exact return control
position and complete bank, without assuming global reachability. -/
namespace Shared.Beeping.NPcoNP.NativePositiveSelectorDirect
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeManyTerminalWindow
open Shared.Beeping.NPcoNP.NativeManyTerminalPositiveMarker
open Shared.Beeping.NPcoNP.NativePositiveControlReturn
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-! Direct state-93 positive selector with a supplied carry and finite bank. -/
theorem terminal_positive_direct_control (t : Int → Bool) (a : Int) (k y r w : Nat) (vs : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ [3,y])))
    (extension : Holds t (a+((encode (List.replicate k 0 ++ [3,y])).length : Int))
      (List.replicate r true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+4+(y : Int)+(r : Int)+4)
      (encode ((w+1)::vs) ++ [false,false]))
    (carry : downHolds t (a+((2*k : Nat):Int)+3) (List.replicate 3 true ++ [false])) :
    let d := a+((2*k : Nat):Int)+4
    let x := d+(0 : Int)+(y : Int)+(r : Int)+4
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧ out (d-4)=true ∧ out (x-1)=false ∧
      Holds out x (encode (w::vs) ++ [true,false,false]) ∧
      (∀ q, d-4<q → q<x-2 → out q=false) ∧ out (x-2)=true ∧
      (∀ q, q<d-4 → out q=t q) ∧
      (∀ q, x+2+((List.replicate w true ++ vs.flatMap
        (fun z => false :: List.replicate (z+1) true)).length : Int)<q → out q=t q) ∧
      silentSegment machine
        (cfg 93 a t)
        (cfg 83 (d-5) out) n := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let x := d+(0 : Int)+(y : Int)+(r : Int)+4
  let suffix := List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  let f := x+2+((suffix.length : Nat):Int)
  let post := spec (clearAt d t) f (suffix.length+2)
  have hw : Holds t a (markerWindow (List.replicate k 0 ++ [0+3,y])) := window
  have hext : Holds t (a+((encode (List.replicate k 0 ++ [0+3,y])).length : Int))
      (List.replicate r true ++ [false]) := extension
  have hbank : Holds t (a+((2*k : Nat):Int)+4+(0:Int)+(y:Int)+(r:Int)+4)
      (encode ((w+1)::vs) ++ [false,false]) := by simpa using bank
  obtain ⟨hpostbank,hframe,hstart⟩ :=
    terminal_window_to_bank t a k 0 y r w vs hw hext hbank
  have hpostbank' : Holds post x (encode (w::vs) ++ [true,false,false]) := by
    simpa only [post,f,x,d,suffix,Nat.cast_zero,add_zero] using hpostbank
  have hframe' : ∀ q, q≠d → (q<x ∨ f<q) → post q=t q := by
    simpa only [post,f,x,d,suffix,Nat.cast_zero,add_zero] using hframe
  obtain ⟨_,hfirst,hsecond⟩ := terminal_scan_words t a k 0 y r hw hext
  have hp1 : t (d+1)=false := by simpa [d,Holds] using hfirst
  have hpost0 : post d=false := by
    change spec (clearAt d t) f (suffix.length+2) d=false
    rw [spec_outside _ _ _ _ (Or.inl (by dsimp [f,x]; omega))]
    simp [clearAt]
  have hpost1 : post (d+1)=false := by
    rw [hframe' _ (by omega) (Or.inl (by dsimp [x]; omega))]
    exact hp1
  have hcarry : downHolds t (d-1) (List.replicate 3 true ++ [false]) := by
    have hp : d-1=a+((2*k : Nat):Int)+3 := by dsimp [d]; omega
    rw [hp]
    exact carry
  have hpostcarry : downHolds post (d-1) (List.replicate 3 true ++ [false]) := by
    have hvals : ∀ q, d-4≤q → q≤d-1 → post q=t q := by
      intro q hq hq'
      exact hframe' q (by omega) (Or.inl (by dsimp [x]; omega))
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,downHolds] at hcarry ⊢
    refine ⟨?_,?_,?_,?_,trivial⟩
    · rw [hvals _ (by omega) (by omega)]; exact hcarry.1
    · rw [hvals _ (by omega) (by omega)]; exact hcarry.2.1
    · rw [hvals _ (by omega) (by omega)]; exact hcarry.2.2.1
    · rw [hvals _ (by omega) (by omega)]; exact hcarry.2.2.2.1
  have hrun : Holds post (d+2) (List.replicate (y+1+r) true ++ [false]) := by
    apply holds_transport t post _ _ (by simpa [d] using hsecond)
    intro q hq hq'
    symm
    apply hframe' q (by omega)
    left
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil,Nat.cast_add,Nat.cast_one] at hq'
    dsimp [x]
    push_cast at hq'
    omega
  obtain ⟨m,stop,out,hm,hstop,hout,heq,hleft,hright,hret⟩ :=
    positive_control_return d (y+1+r) post (by omega) hpostcarry hpost0 hpost1 hrun
  have hx : d+((y+1+r : Nat):Int)+2=x-1 := by dsimp [x]; omega
  have hblank : out (x-1)=false := by
    rw [←hx,hright _ (by omega),hframe' _ (by omega) (Or.inl (by dsimp [x]; omega))]
    have hzero := holds_get t (d+2) (List.replicate (y+1+r) true ++ [false])
      (by simpa [d] using hsecond) (y+1+r) (by simp)
    have he : d+2+((y+1+r : Nat):Int)=d+((y+1+r : Nat):Int)+2 := by omega
    rw [he] at hzero
    simpa using hzero
  have hbankout : Holds out x (encode (w::vs) ++ [true,false,false]) := by
    apply holds_of_right_frame post out x _ hpostbank'
    intro q hq
    apply hright q
    rw [hx]
    omega
  have hstop' : stop=x-2 := by rw [hstop]; dsimp [x]; omega
  have hstopbit : out (x-2)=true := by
    rw [heq, ←hstop']
    simp [put]
  have hcorr : ∀ q, d-4<q → q<x-2 → out q=false := by
    intro q hlow hhigh
    rw [heq, hstop']
    simp only [put, clearRange, result, cleared]
    split_ifs <;> first
      | rfl
      | omega
      | (have he : q=d ∨ q=d+1 := by omega
         rcases he with he | he
         · simpa [he] using hpost0
         · simpa [he] using hpost1)
  have hleft' : ∀ q, q<d-4 → out q=t q := by
    intro q hq
    rw [hleft q hq,hframe' q (by omega) (Or.inl (by dsimp [x]; omega))]
  have hright' : ∀ q, f<q → out q=t q := by
    intro q hq
    rw [hright q (by dsimp [f,x,suffix] at hq ⊢; omega),
      hframe' q (by dsimp [f,x,suffix] at hq ⊢; omega) (Or.inr hq)]
  have hstart' : silentSegment machine
      (cfg 93 a t)
      (cfg 23 (d+((y+1+r : Nat):Int)+1) post)
      (2*k+y+r+2*suffix.length+16) := by
    have hpos : d+((y+1+r : Nat):Int)+1=x-2 := by dsimp [x]; omega
    simpa only [Nat.zero_add,Nat.cast_zero,add_zero,hpos,post,d,x,suffix,f] using hstart
  have hall := segAdd machine _ _ _ _ m hstart' hret
  exact ⟨_,out,by omega,hout,hblank,hbankout,hcorr,hstopbit,hleft',hright',hall⟩


#print axioms terminal_positive_direct_control
end Shared.Beeping.NPcoNP.NativePositiveSelectorDirect
