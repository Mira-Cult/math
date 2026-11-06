import Shared.Beeping.NPcoNP.NativeReturnBelow83Exact
import Shared.Beeping.NPcoNP.NativeHalfBankFirst
import Shared.Beeping.NPcoNP.NativeManyScanBarrier
import Shared.Beeping.NPcoNP.NativeManySelectorRoundtrip

/-! The positive-bank return preserves its control prefix and the encoded
bank suffix beyond the first post-update separator. -/
namespace Shared.Beeping.NPcoNP.NativeManyTerminalPositiveMarker
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeManySelectorBank
open Shared.Beeping.NPcoNP.NativeManySelectorRoundtrip
open Shared.Beeping.NPcoNP.NativeManyWindowBank
open Shared.Beeping.NPcoNP.NativeManyTerminalWindow
open Shared.Beeping.NPcoNP.NativeManyScanBarrier
open Shared.Beeping.NPcoNP.NativeReturnBelow83Exact
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- A preserved right ray preserves every finite word placed on that ray. -/
theorem holds_of_right_frame (t u : Int → Bool) (a : Int) (xs : List Bool)
    (ht : Holds t a xs) (hf : ∀ q, a≤q → u q=t q) : Holds u a xs := by
  induction xs generalizing a with
  | nil => trivial
  | cons b xs ih =>
    change t a=b ∧ Holds t (a+1) xs at ht
    change u a=b ∧ Holds u (a+1) xs
    exact ⟨(hf a (by omega)).trans ht.1, ih (a+1) ht.2 (by intro q hq; apply hf; omega)⟩

/-- The positive return preserves the complete updated bank and its preceding
zero, in addition to its earlier control prefix and right marker. -/
theorem terminal_positive_selector_bank (t : Int → Bool) (a z b : Int)
    (k v y r w : Nat) (vs : List Nat)
    (hl : (List.replicate k 0 ++ [v+3,y]).length=14)
    (marker : t (a-1)=true)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ [v+3,y])))
    (extension : Holds t (a+((encode (List.replicate k 0 ++ [v+3,y])).length : Int))
      (List.replicate r true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+(r : Int)+4)
      (encode ((w+1)::vs) ++ [false,false]))
    (left : ∀ q, q≤z → t q=false) (right : ∀ q, b≤q → t q=false) :
    let d := a+((2*k : Nat):Int)+4
    let x := d+(v : Int)+(y : Int)+(r : Int)+4
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=83 ∧ e.head+1<d ∧
      e.tape (e.head+1)=true ∧ (∀ q, q≤e.head → e.tape q=t q) ∧
      e.tape (x+((w+2 : Nat):Int))=true ∧
      Holds e.tape (x+((w+2 : Nat):Int)) (encode vs ++ [true,false,false]) ∧
      e.tape (x-1)=false ∧ e.tape x=true ∧
      Holds e.tape x (encode (w::vs) ++ [true,false,false]) ∧
      (∀ q, x-1≤q → e.tape q=
        spec (clearAt d t)
          (x+2+((List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)).length : Int))
          ((List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)).length+2) q) ∧
      silentSegment machine
        (cfg 83 (a+((encode (List.replicate k 0 ++ [v+3,y])).length : Int)-1) t) e n := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let x := d+(v : Int)+(y : Int)+(r : Int)+4
  let suffix := List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  let f := x+2+((suffix.length : Nat):Int)
  let out := spec (clearAt d t) f (suffix.length+2)
  obtain ⟨hbank,hframe,hstart⟩ := terminal_selector_to_bank t a k v y r w vs hl marker window extension bank
  have hbank' : Holds out x (encode (w::vs) ++ [true,false,false]) := hbank
  let z' := min z (d-1)
  let b' := max b (f+1)
  have hd : d<x := by dsimp [x]; omega
  have hxf : x≤f := by dsimp [f]; omega
  have hleft : ∀ q, q≤z' → out q=false := by
    intro q hq
    have hqd : q<d := by dsimp [z'] at hq; omega
    have hh : out q=t q := hframe q (by omega) (Or.inl (by omega))
    rw [hh]
    apply left q
    dsimp [z'] at hq
    omega
  have hright : ∀ q, b'≤q → out q=false := by
    intro q hq
    have hqf : f<q := by dsimp [b'] at hq; omega
    have hh : out q=t q := hframe q (by omega) (Or.inr hqf)
    rw [hh]
    apply right q
    dsimp [b'] at hq
    omega
  obtain ⟨_hhead,hfirst,hsecond⟩ := terminal_scan_words t a k v y r window extension
  have hagree : ∀ q, d+1≤q → q≤d+(v : Int)+((y+1+r : Nat):Int)+2 → out q=t q := by
    intro q hq hq'
    apply hframe q (by omega)
    left
    dsimp [x]
    push_cast at hq'
    omega
  have hsafe : ∀ q, d+2≤q → q≤x-2 → out q=false → out (q-1)=true := by
    intro q hq htop hz
    apply two_word_barrier t out d v (y+1+r) (by omega) hfirst hsecond hagree q hq
    · dsimp [x] at htop
      push_cast
      omega
    · exact hz
  have htail : Holds out (x+((w+2 : Nat):Int)) (encode vs ++ [true,false,false]) := by
    have ht := holds_append_tail out x (block w) (encode vs ++ [true,false,false])
      (by simpa [encode,List.append_assoc] using hbank')
    simpa [block_length] using ht
  have hnext : out (x+((w+2 : Nat):Int))=true := by
    cases vs with
    | nil => simpa [encode,Holds] using htail.1
    | cons v vs => simpa [encode,block,List.replicate_succ,Holds] using htail.1
  have hlast : t (x-2)=true := by
    let i := y+r
    have hi : i<(List.replicate (y+1+r) true ++ [false]).length := by dsimp [i]; simp
    have hc := holds_get t (d+(v : Int)+2) _ hsecond i hi
    have hb : (List.replicate (y+1+r) true ++ [false])[i]'hi=true := by
      rw [List.getElem_append_left (by dsimp [i]; simp)]
      simp
    rw [hb] at hc
    have he : d+(v : Int)+2+(i : Int)=x-2 := by dsimp [x,i]; omega
    rw [he] at hc
    exact hc
  have hblank : t (x-1)=false := by
    let i := y+1+r
    have hi : i<(List.replicate (y+1+r) true ++ [false]).length := by dsimp [i]; simp
    have hc := holds_get t (d+(v : Int)+2) _ hsecond i hi
    have hb : (List.replicate (y+1+r) true ++ [false])[i]'hi=false := by dsimp [i]; simp
    rw [hb] at hc
    have he : d+(v : Int)+2+(i : Int)=x-1 := by dsimp [x,i]; omega
    rw [he] at hc
    exact hc
  have houtlast : out (x-2)=true := by
    have hh : out (x-2)=t (x-2) := hframe (x-2) (by dsimp [x]; omega) (Or.inl (by omega))
    rw [hh]
    exact hlast
  have houtblank : out (x-1)=false := by
    have hh : out (x-1)=t (x-1) := hframe (x-1) (by dsimp [x]; omega) (Or.inl (by omega))
    rw [hh]
    exact hblank
  obtain ⟨m,j,l,n,stop,final,hm,hn,hbelow,hhead,hstop,hmark,hzero,hones,
    _heq,hframe',hright,hlimit,_hretain,hscan,hcarry⟩ :=
    state23_to83_below_exact (x-2) d (x-2) z' b' out hleft hright hsafe (by omega) houtlast
  have hstopbefore : stop<x-1 :=
    hlimit (x-1) (by omega) (by omega) houtblank
  have hbankframe : ∀ q, x-1≤q → final q=out q := by
    intro q hq
    exact hright q (by omega) (by omega)
  let mark := (x-2)-(m : Int)-(j : Int)
  let e : Config 284 := cfg 83 (mark-1) final
  have hemark : e.tape (x+((w+2 : Nat):Int))=true := by
    change final (x+((w+2 : Nat):Int))=true
    rw [hbankframe _ (by push_cast; omega)]
    exact hnext
  have htailframe : ∀ q, x+((w+2 : Nat):Int)≤q → final q=out q := by
    intro q hq
    apply hbankframe q
    push_cast at hq
    omega
  have htailfinal : Holds e.tape (x+((w+2 : Nat):Int)) (encode vs ++ [true,false,false]) := by
    change Holds final (x+((w+2 : Nat):Int)) (encode vs ++ [true,false,false])
    exact holds_of_right_frame out final _ _ htail htailframe
  have heblank : e.tape (x-1)=false := by
    change final (x-1)=false
    rw [hbankframe _ (by omega)]
    exact houtblank
  have hefull : Holds e.tape x (encode (w::vs) ++ [true,false,false]) := by
    change Holds final x (encode (w::vs) ++ [true,false,false])
    apply holds_of_right_frame out final x _ hbank'
    intro q hq
    exact hbankframe q (by omega)
  have hefirst : e.tape x=true := bank_head e.tape x w vs [true,false,false] hefull
  have heframe : ∀ q, x-1≤q → e.tape q=out q := by
    intro q hq
    exact hbankframe q hq
  have hprefix : ∀ q, q≤e.head → e.tape q=t q := by
    intro q hq
    calc
      e.tape q = out q := hframe' q (by change q≤mark-1 at hq; omega)
      _ = t q := hframe q (by change q≤mark-1 at hq; omega) (Or.inl (by change q≤mark-1 at hq; omega))
  let n0 := (encode (List.replicate k 0 ++ [v+3,y])).length+1+
    (2*k+v+y+r+2*suffix.length+16)
  have hret := segAdd machine _ _ _ m ((j+1)+(l+1)+n) hscan hcarry
  have hall := segAdd machine _ _ _ n0 (m+((j+1)+(l+1)+n)) hstart hret
  refine ⟨n0+(m+((j+1)+(l+1)+n)),e,by omega,rfl,?_,?_,hprefix,hemark,htailfinal,heblank,hefirst,hefull,heframe,?_⟩
  · change mark-1+1<d
    dsimp [mark]
    omega
  · change final (mark-1+1)=true
    simpa [mark] using hmark
  · simpa only [e,mark] using hall


/-- For a prepared terminal fourteen-block window with its finite extension
and a positive following bank,
the finite silent roundtrip returns with a marker strictly left of the
cleared selector cell, preserves the preceding control prefix, and retains
the encoded bank suffix and its first one beyond the first separator. -/
theorem terminal_positive_selector_marker (t : Int → Bool) (a z b : Int)
    (k v y r w : Nat) (vs : List Nat)
    (hl : (List.replicate k 0 ++ [v+3,y]).length=14)
    (marker : t (a-1)=true)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ [v+3,y])))
    (extension : Holds t (a+((encode (List.replicate k 0 ++ [v+3,y])).length : Int))
      (List.replicate r true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+(r : Int)+4)
      (encode ((w+1)::vs) ++ [false,false]))
    (left : ∀ q, q≤z → t q=false) (right : ∀ q, b≤q → t q=false) :
    let d := a+((2*k : Nat):Int)+4
    let x := d+(v : Int)+(y : Int)+(r : Int)+4
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=83 ∧ e.head+1<d ∧
      e.tape (e.head+1)=true ∧ (∀ q, q≤e.head → e.tape q=t q) ∧
      e.tape (x+((w+2 : Nat):Int))=true ∧
      Holds e.tape (x+((w+2 : Nat):Int)) (encode vs ++ [true,false,false]) ∧
      silentSegment machine
        (cfg 83 (a+((encode (List.replicate k 0 ++ [v+3,y])).length : Int)-1) t) e n := by
  obtain ⟨n,e,hn,hs,hbelow,hmark,hprefix,hright,htail,_hblank,_hfirst,_hbank,_hframe,hseg⟩ :=
    terminal_positive_selector_bank t a z b k v y r w vs hl marker window extension bank left right
  exact ⟨n,e,hn,hs,hbelow,hmark,hprefix,hright,htail,hseg⟩

#print axioms holds_of_right_frame
#print axioms terminal_positive_selector_bank
#print axioms terminal_positive_selector_marker
end Shared.Beeping.NPcoNP.NativeManyTerminalPositiveMarker
