import Shared.Beeping.NPcoNP.NativeManyDispatchBank
import Shared.Beeping.NPcoNP.NativeHalfMarkerMany
import Shared.Beeping.NPcoNP.NativeIncBank

/-! A selector may end inside the second scanned one-run, and its omitted final delimiter may be occupied by a one. The extra finite run and
its stopping zero must be supplied; it cannot be read from the window alone. -/
namespace Shared.Beeping.NPcoNP.NativeManyTerminalWindow
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
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeManyDispatchBank
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem terminal_many_window (k v y : Nat) :
    markerWindow (List.replicate k 0 ++ [v+3,y]) =
      false :: (encode (List.replicate k 0) ++ block (v+3) ++ List.replicate (y+1) true) := by
  apply List.append_cancel_right (bs := [false])
  have h := markerWindow_append_zero (List.replicate k 0 ++ [v+3,y])
  simpa [encode_append,encode,block,List.append_assoc] using h

/-- An explicit one-run starting at the omitted delimiter extends the
second scan. Its final zero is the progress witness. -/
theorem terminal_scan_words (t : Int → Bool) (a : Int) (k v y r : Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ [v+3,y])))
    (extension : Holds t (a+((encode (List.replicate k 0 ++ [v+3,y])).length : Int))
      (List.replicate r true ++ [false])) :
    let d := a+((2*k : Nat):Int)+4
    t d=true ∧
    Holds t (d+1) (List.replicate v true ++ [false]) ∧
    Holds t (d+(v : Int)+2) (List.replicate (y+1+r) true ++ [false]) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let b := a+1+((2*k : Nat):Int)
  rw [terminal_many_window] at window
  have hprefix : Holds t b (block (v+3) ++ List.replicate (y+1) true) := by
    have hh := holds_append_tail t (a+1) (encode (List.replicate k 0))
      (block (v+3) ++ List.replicate (y+1) true) (by simpa [List.append_assoc] using window.2)
    have hl : (encode (List.replicate k 0)).length=2*k := zeros_length k
    simpa only [hl,b] using hh
  have hb : Holds t b (block (v+3)) :=
    holds_prefix_word t b (block (v+3)) (List.replicate (y+1) true) hprefix
  have hsize : 3<(block (v+3)).length := by simp [block_length]
  have hpoint := holds_get t b (block (v+3)) hb 3 hsize
  have hhead : t d=true := by
    have he : b+(3 : Int)=d := by dsimp [b,d]; omega
    norm_num only [Nat.cast_ofNat] at hpoint
    rw [he] at hpoint
    simpa [block] using hpoint
  have hblock : block (v+3) ++ List.replicate (y+1) true =
      List.replicate 4 true ++ ((List.replicate v true ++ [false]) ++ List.replicate (y+1) true) := by
    have hnum : v+3+1=4+v := by omega
    simp [block,hnum,List.replicate_add,List.append_assoc]
  rw [hblock] at hprefix
  have hwords := holds_append_tail t b (List.replicate 4 true)
    ((List.replicate v true ++ [false]) ++ List.replicate (y+1) true) hprefix
  have hepos : b+((List.replicate 4 true).length : Int)=d+1 := by simp [b,d]; omega
  rw [hepos] at hwords
  have hfirst := holds_prefix_word t (d+1) (List.replicate v true ++ [false]) _ hwords
  have hbase := holds_append_tail t (d+1) (List.replicate v true ++ [false])
    (List.replicate (y+1) true) hwords
  have hpos : d+1+(((List.replicate v true ++ [false]).length : Nat):Int)=d+(v : Int)+2 := by simp; omega
  rw [hpos] at hbase
  have hlen : (encode (List.replicate k 0 ++ [v+3,y])).length=2*k+v+y+7 := by
    simp [encode_append,encode,zeros_length,block_length]
    omega
  rw [hlen] at extension
  have hend : d+(v : Int)+2+((List.replicate (y+1) true).length : Int)=
      a+((2*k+v+y+7 : Nat):Int) := by simp [d]; push_cast; omega
  have hext : Holds t (d+(v : Int)+2+((List.replicate (y+1) true).length : Int))
      (List.replicate r true ++ [false]) := by rw [hend]; exact extension
  have hall := holds_append_intro t (d+(v : Int)+2) (List.replicate (y+1) true)
    (List.replicate r true ++ [false]) hbase hext
  refine ⟨hhead,hfirst,?_⟩
  simpa [List.replicate_add,List.append_assoc,d] using hall

/-- The terminal selector has an independently supplied finite extension;
together with the prepared following bank this gives exact silent progress. -/
theorem terminal_window_to_bank (t : Int → Bool) (a : Int) (k v y r w : Nat) (vs : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ [v+3,y])))
    (extension : Holds t (a+((encode (List.replicate k 0 ++ [v+3,y])).length : Int))
      (List.replicate r true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+(r : Int)+4)
      (encode ((w+1)::vs) ++ [false,false])) :
    let d := a+((2*k : Nat):Int)+4
    let x := d+(v : Int)+(y : Int)+(r : Int)+4
    let u := clearAt d t
    let suffix := List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    let f := x+2+suffix.length
    let out := spec u f (suffix.length+2)
    Holds out x (encode (w::vs) ++ [true,false,false]) ∧
    (∀ p, p≠d → (p<x ∨ f<p) → out p=t p) ∧
    silentSegment machine (cfg 93 a t) (cfg 23 (x-2) out)
      (2*k+v+y+r+2*suffix.length+16) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let x := d+(v : Int)+(y : Int)+(r : Int)+4
  let u := clearAt d t
  let suffix := List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  let f := x+2+((suffix.length : Nat):Int)
  let out := spec u f (suffix.length+2)
  obtain ⟨hhead,hfirst,hsecond⟩ := terminal_scan_words t a k v y r window extension
  have hhead' : t d=true := hhead
  have hfirst' : Holds t (d+1) (List.replicate v true ++ [false]) := hfirst
  have hsecond' : Holds t (d+(v : Int)+2) (List.replicate (y+1+r) true ++ [false]) := hsecond
  have he : d+(v : Int)+((y+1+r : Nat):Int)+3=x := by dsimp [x]; push_cast; omega
  have hbank : Holds t (d+(v : Int)+((y+1+r : Nat):Int)+3)
      (encode ((w+1)::vs) ++ [false,false]) := by rw [he]; exact bank
  obtain ⟨hresult,hframe,hdispatch⟩ :=
    dispatch260_bank v (y+1+r) w vs d t hhead' hfirst' hsecond' hbank
  have hdispatch' : silentSegment machine (cfg 260 d t) (cfg 23 (x-2) out)
      (v+(y+1+r)+2*suffix.length+11) := by
    simpa only [he,x,u,suffix,f,out] using hdispatch
  have hw : Holds t a (markerWindow (List.replicate k 0 ++ ((v+1)+2)::[y])) := by
    simpa [Nat.add_assoc] using window
  have hscan := marker_window_to_ge_two t a k (v+1) [y] (by simp) hw
  have hall := segAdd machine _ _ _ (2*k+4) (v+(y+1+r)+2*suffix.length+11) hscan hdispatch'
  have hc : 2*k+4+(v+(y+1+r)+2*suffix.length+11)=2*k+v+y+r+2*suffix.length+16 := by omega
  rw [hc] at hall
  rw [he] at hresult hframe
  refine ⟨?_,?_,?_⟩
  · simpa only [d,x,u,suffix,f,out] using hresult
  · simpa only [d,x,u,suffix,f,out] using hframe
  · simpa only [d,x,u,suffix,f,out] using hall

/-- The matching fourteen-block selector entry is included. The extension
and its terminating zero are still explicit inputs. -/
theorem terminal_selector_to_bank (t : Int → Bool) (a : Int) (k v y r w : Nat) (vs : List Nat)
    (hl : (List.replicate k 0 ++ [v+3,y]).length=14)
    (marker : t (a-1)=true)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ [v+3,y])))
    (extension : Holds t (a+((encode (List.replicate k 0 ++ [v+3,y])).length : Int))
      (List.replicate r true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+(r : Int)+4)
      (encode ((w+1)::vs) ++ [false,false])) :
    let selector := List.replicate k 0 ++ [v+3,y]
    let d := a+((2*k : Nat):Int)+4
    let x := d+(v : Int)+(y : Int)+(r : Int)+4
    let u := clearAt d t
    let suffix := List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    let f := x+2+suffix.length
    let out := spec u f (suffix.length+2)
    Holds out x (encode (w::vs) ++ [true,false,false]) ∧
    (∀ p, p≠d → (p<x ∨ f<p) → out p=t p) ∧
    silentSegment machine (cfg 83 (a+((encode selector).length : Int)-1) t)
      (cfg 23 (x-2) out) ((encode selector).length+1+(2*k+v+y+r+2*suffix.length+16)) := by
  dsimp only
  let selector := List.replicate k 0 ++ [v+3,y]
  let suffix := List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  have hentry := marker_window_to93 t a selector hl window marker
  obtain ⟨hresult,hframe,hbody⟩ := terminal_window_to_bank t a k v y r w vs window extension bank
  exact ⟨hresult,hframe,segAdd machine _ _ _ ((encode selector).length+1)
    (2*k+v+y+r+2*suffix.length+16) hentry hbody⟩

#print axioms terminal_many_window
#print axioms terminal_scan_words
#print axioms terminal_selector_to_bank
end Shared.Beeping.NPcoNP.NativeManyTerminalWindow
