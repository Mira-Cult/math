import Shared.Beeping.NPcoNP.NativeManyDispatchBank
import Shared.Beeping.NPcoNP.NativeHalfMarkerMany

/-! A positive selector window determines the two paid scan words.
The remaining bank and trailing blanks are supplied explicitly. -/
namespace Shared.Beeping.NPcoNP.NativeManyWindowBank
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfMarkerMany
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeManyDispatchBank
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- For a selector value at least three, the remaining part of its block
and the entire next block are exactly the two scanned words. -/
theorem many_scan_words (t : Int → Bool) (a : Int) (k v y z : Nat) (zs : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ (v+3)::y::z::zs))) :
    let d := a+((2*k : Nat):Int)+4
    Holds t (d+1) (List.replicate v true ++ [false]) ∧
    Holds t (d+(v : Int)+2) (List.replicate (y+1) true ++ [false]) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let b := a+1+((2*k : Nat):Int)
  obtain ⟨tail,he⟩ := marker_two_blocks k (v+3) y z zs
  rw [he] at window
  have hprefix : Holds t b (block (v+3) ++ (block y ++ tail)) := by
    have hh := holds_append_tail t (a+1) (encode (List.replicate k 0))
      (block (v+3) ++ (block y ++ tail)) (by simpa [List.append_assoc] using window.2)
    have hl : (encode (List.replicate k 0)).length=2*k := zeros_length k
    simpa only [hl,b] using hh
  have hblock : block (v+3) ++ (block y ++ tail) =
      List.replicate 4 true ++ ((List.replicate v true ++ [false]) ++ (block y ++ tail)) := by
    have hnum : v+3+1=4+v := by omega
    simp [block,hnum,List.replicate_add,List.append_assoc]
  rw [hblock] at hprefix
  have hwords := holds_append_tail t b (List.replicate 4 true)
    ((List.replicate v true ++ [false]) ++ (block y ++ tail)) hprefix
  have hepos : b+((List.replicate 4 true).length : Int)=d+1 := by simp [b,d]; omega
  rw [hepos] at hwords
  have hfirst := holds_prefix_word t (d+1) (List.replicate v true ++ [false]) (block y ++ tail) hwords
  have hsecond := holds_append_tail t (d+1) (List.replicate v true ++ [false]) (block y ++ tail) hwords
  have hsecond' := holds_prefix_word t _ (block y) tail hsecond
  have hp : d+1+(((List.replicate v true ++ [false]).length : Nat):Int)=d+(v : Int)+2 := by simp; omega
  rw [hp] at hsecond'
  exact ⟨hfirst,by simpa [d,block] using hsecond'⟩

/-- A value-at-least-three selector window supplies both physical scan
words. Given the positive following bank and its two trailing blanks, the
complete window-to-bank segment is silent, finite and tape-framed. -/
theorem window_to_bank (t : Int → Bool) (a : Int) (k v y w : Nat) (zs vs : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ (v+3)::y::(w+1)::zs)))
    (bank : Holds t (a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+4)
      (encode ((w+1)::vs) ++ [false,false])) :
    let d := a+((2*k : Nat):Int)+4
    let x := d+(v : Int)+(y : Int)+4
    let u := clearAt d t
    let suffix := List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    let f := x+2+suffix.length
    let out := spec u f (suffix.length+2)
    Holds out x (encode (w::vs) ++ [true,false,false]) ∧
    (∀ p, p≠d → (p<x ∨ f<p) → out p=t p) ∧
    silentSegment machine (cfg 93 a t) (cfg 23 (x-2) out)
      (2*k+v+y+2*suffix.length+16) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let x := d+(v : Int)+(y : Int)+4
  let u := clearAt d t
  let suffix := List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  let f := x+2+((suffix.length : Nat):Int)
  let out := spec u f (suffix.length+2)
  have hhead : t d=true := many_marker_head t a k v y (w+1) zs window
  obtain ⟨hfirst,hsecond⟩ := many_scan_words t a k v y (w+1) zs window
  have hfirst' : Holds t (d+1) (List.replicate v true ++ [false]) := hfirst
  have hsecond' : Holds t (d+(v : Int)+2) (List.replicate (y+1) true ++ [false]) := hsecond
  have hbank : Holds t (d+(v : Int)+((y+1 : Nat):Int)+3)
      (encode ((w+1)::vs) ++ [false,false]) := by
    have he : d+(v : Int)+((y+1 : Nat):Int)+3=x := by dsimp [x]; push_cast; omega
    rw [he]
    exact bank
  obtain ⟨hresult,hframe,hdispatch⟩ :=
    dispatch260_bank v (y+1) w vs d t hhead hfirst' hsecond' hbank
  have hdispatch' : silentSegment machine (cfg 260 d t) (cfg 23 (x-2) out)
      (v+(y+1)+2*suffix.length+11) := by
    have he : d+(v : Int)+((y+1 : Nat):Int)+3=x := by dsimp [x]; push_cast; omega
    simpa only [he,x,u,suffix,f,out] using hdispatch
  have hw : Holds t a (markerWindow (List.replicate k 0 ++ ((v+1)+2)::y::(w+1)::zs)) := by
    simpa [Nat.add_assoc] using window
  have hscan := marker_window_to_ge_two t a k (v+1) (y::(w+1)::zs) (by simp) hw
  have hall := segAdd machine _ _ _ (2*k+4) (v+(y+1)+2*suffix.length+11) hscan hdispatch'
  have hc : 2*k+4+(v+(y+1)+2*suffix.length+11)=2*k+v+y+2*suffix.length+16 := by omega
  rw [hc] at hall
  have he : d+(v : Int)+((y+1 : Nat):Int)+3=x := by dsimp [x]; push_cast; omega
  rw [he] at hresult hframe
  refine ⟨?_,?_,?_⟩
  · simpa only [d,x,u,suffix,f,out] using hresult
  · simpa only [d,x,u,suffix,f,out] using hframe
  · simpa only [d,x,u,suffix,f,out] using hall

#print axioms many_scan_words
#print axioms window_to_bank
end Shared.Beeping.NPcoNP.NativeManyWindowBank
