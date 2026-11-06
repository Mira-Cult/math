import Shared.Beeping.NPcoNP.NativeCarryReachable83
import Shared.Beeping.NPcoNP.NativeManyZeroSelector
import Shared.Beeping.NPcoNP.NativeManySelectorBank
import Shared.Beeping.NPcoNP.NativeManyZeroReachable

/-! A prepared positive-control selector returns to state 83 for either
value of the following bank. Both blank tails and the local layout are
explicit; no recurrence or graph correspondence is asserted. -/
namespace Shared.Beeping.NPcoNP.NativeManySelectorRoundtrip
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeCarryReturn83
open Shared.Beeping.NPcoNP.NativeCarryReachable83
open Shared.Beeping.NPcoNP.NativeManyZeroSelector
open Shared.Beeping.NPcoNP.NativeManySelectorBank
open Shared.Beeping.NPcoNP.NativeManyTerminalWindow
open Shared.Beeping.NPcoNP.NativeManyZeroReachable
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

theorem bank_head (t : Int → Bool) (x : Int) (v : Nat) (vs : List Nat) (extra : List Bool)
    (bank : Holds t x (encode (v::vs) ++ extra)) : t x=true := by
  simp only [encode,block,List.replicate_succ,List.cons_append,Holds] at bank
  exact bank.1

/-- Whole selector-to-selector finite silent progress for either value of
the following unary bank. The bank and control layouts are premises. -/
theorem selector_roundtrip (t : Int → Bool) (a z b : Int) (k v y value : Nat) (zs vs : List Nat)
    (hl : (List.replicate k 0 ++ (v+3)::y::value::zs).length=14)
    (marker : t (a-1)=true)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ (v+3)::y::value::zs)))
    (bank : Holds t (a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+4)
      (encode (value::vs) ++ [false,false]))
    (left : ∀ q, q≤z → t q=false) (right : ∀ q, b≤q → t q=false) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=83 ∧ e.tape (e.head+1)=true ∧
      silentSegment machine
        (cfg 83 (a+((encode (List.replicate k 0 ++ (v+3)::y::value::zs)).length : Int)-1) t) e n := by
  let selector := List.replicate k 0 ++ (v+3)::y::value::zs
  let d := a+((2*k : Nat):Int)+4
  let x := d+(v : Int)+(y : Int)+4
  cases value with
  | zero =>
    obtain ⟨bound,hbound⟩ := tail_bound t x z left
    have htail : ∀ q, q≤a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+3-(bound : Int) → t q=false := by
      intro q hq
      apply hbound q
      dsimp [x,d]
      omega
    obtain ⟨m,j,hm,_hmb,hj,_hjb,hbank,_hframe,hstart⟩ :=
      selector_zero_tail t a k v y bound zs vs hl marker window bank htail
    let pos := x-1-(m : Int)
    let u := clearAt d t
    let out := clearRange u (pos-(j : Int)+2) (pos+1)
    have hbank' : Holds out x (encode (0::vs) ++ [false,false]) := hbank
    have hone : out x=true := bank_head out x 0 vs [false,false] hbank'
    have hleft : ∀ q, q≤z → out q=false := by
      intro q hq
      have hh := left q hq
      simp [out,u,clearRange,clearAt,hh]
    have hright : ∀ q, b≤q → out q=false := by
      intro q hq
      have hh := right q hq
      simp [out,u,clearRange,clearAt,hh]
    have hp : pos-(j : Int)<x := by dsimp [pos]; omega
    obtain ⟨j2,l2,n2,stop,final,hn2,_hpos,_hstop,hmark,_hz,_hones,_heq,_hprefix,hreturn⟩ :=
      carry_to83 (pos-(j : Int)) x z b out hleft hright hp hone
    let e : Config 284 := cfg 83 (pos-(j : Int)-(j2 : Int)-1) final
    have hall := segAdd machine _ _ _ ((encode selector).length+1+(2*k+v+y+m+j+11))
      ((j2+1)+(l2+1)+n2) hstart hreturn
    refine ⟨((encode selector).length+1+(2*k+v+y+m+j+11))+((j2+1)+(l2+1)+n2),
      e,by omega,rfl,?_,?_⟩
    · simpa [e,cfg] using hmark
    · simpa only [selector,d,x,pos,u,out,e,Nat.add_assoc] using hall
  | succ w =>
    have hl' : (List.replicate k 0 ++ (v+3)::y::(w+1)::zs).length=14 := by simpa using hl
    have hw : Holds t a (markerWindow (List.replicate k 0 ++ (v+3)::y::(w+1)::zs)) := by simpa using window
    have hb : Holds t (a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+4)
        (encode ((w+1)::vs) ++ [false,false]) := by simpa using bank
    obtain ⟨hbank,hframe,hstart⟩ := selector_to_bank t a k v y w zs vs hl' marker hw hb
    let suffix := List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    let f := x+2+((suffix.length : Nat):Int)
    let out := spec (clearAt d t) f (suffix.length+2)
    have hbank' : Holds out x (encode (w::vs) ++ [true,false,false]) := hbank
    have hone : out x=true := bank_head out x w vs [true,false,false] hbank'
    let z' := min z (d-1)
    let b' := max b (f+1)
    have hd : d<x := by dsimp [x]; omega
    have hxf : x≤f := by dsimp [f]; omega
    have hleft : ∀ q, q≤z' → out q=false := by
      intro q hq
      have hqd : q<d := by dsimp [z'] at hq; omega
      have hqx : q<x := by omega
      have hh : out q=t q := hframe q (by omega) (Or.inl hqx)
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
    obtain ⟨m,j,l,n,final,hm,hn,hmark,_hprefix,hreturn⟩ :=
      state23_to83 (x-2) x z' b' out hleft hright (by omega) hone
    let e : Config 284 := cfg 83 (x-2-(m : Int)-(j : Int)-1) final
    have hpos : 0 < (encode (List.replicate k 0 ++ (v+3)::y::(w+1)::zs)).length+1+
        (2*k+v+y+2*suffix.length+16) := by omega
    have hall := segAdd machine _ _ _
      ((encode (List.replicate k 0 ++ (v+3)::y::(w+1)::zs)).length+1+(2*k+v+y+2*suffix.length+16))
      (m+(j+1)+(l+1)+n) hstart hreturn
    refine ⟨((encode (List.replicate k 0 ++ (v+3)::y::(w+1)::zs)).length+1+
      (2*k+v+y+2*suffix.length+16))+(m+(j+1)+(l+1)+n),e,by omega,rfl,?_,?_⟩
    · simpa [e,cfg] using hmark
    · simpa only [selector,Nat.succ_eq_add_one,d,x,suffix,f,out,e,Nat.add_assoc] using hall

/-- Terminal-window counterpart. The supplied finite extension provides
both the remainder of the last scan and its stopping zero. -/
theorem terminal_roundtrip (t : Int → Bool) (a z b : Int) (k v y r value : Nat) (vs : List Nat)
    (hl : (List.replicate k 0 ++ [v+3,y]).length=14)
    (marker : t (a-1)=true)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ [v+3,y])))
    (extension : Holds t (a+((encode (List.replicate k 0 ++ [v+3,y])).length : Int))
      (List.replicate r true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+(r : Int)+4)
      (encode (value::vs) ++ [false,false]))
    (left : ∀ q, q≤z → t q=false) (right : ∀ q, b≤q → t q=false) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=83 ∧ e.tape (e.head+1)=true ∧
      silentSegment machine
        (cfg 83 (a+((encode (List.replicate k 0 ++ [v+3,y])).length : Int)-1) t) e n := by
  let selector := List.replicate k 0 ++ [v+3,y]
  let d := a+((2*k : Nat):Int)+4
  let x := d+(v : Int)+(y : Int)+(r : Int)+4
  cases value with
  | zero =>
    obtain ⟨bound,hbound⟩ := tail_bound t x z left
    have htail : ∀ q, q≤a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+(r : Int)+3-(bound : Int) → t q=false := by
      intro q hq
      apply hbound q
      dsimp [x,d]
      omega
    obtain ⟨m,j,hm,_hmb,hj,_hjb,hbank,_hframe,hstart⟩ :=
      terminal_selector_zero_tail t a k v y r bound vs hl marker window extension bank htail
    let pos := x-1-(m : Int)
    let u := clearAt d t
    let out := clearRange u (pos-(j : Int)+2) (pos+1)
    have hbank' : Holds out x (encode (0::vs) ++ [false,false]) := hbank
    have hone : out x=true := bank_head out x 0 vs [false,false] hbank'
    have hleft : ∀ q, q≤z → out q=false := by
      intro q hq
      have hh := left q hq
      simp [out,u,clearRange,clearAt,hh]
    have hright : ∀ q, b≤q → out q=false := by
      intro q hq
      have hh := right q hq
      simp [out,u,clearRange,clearAt,hh]
    have hp : pos-(j : Int)<x := by dsimp [pos]; omega
    obtain ⟨j2,l2,n2,stop,final,hn2,_hpos,_hstop,hmark,_hz,_hones,_heq,_hprefix,hreturn⟩ :=
      carry_to83 (pos-(j : Int)) x z b out hleft hright hp hone
    let e : Config 284 := cfg 83 (pos-(j : Int)-(j2 : Int)-1) final
    have hall := segAdd machine _ _ _ ((encode selector).length+1+(2*k+v+y+r+m+j+11))
      ((j2+1)+(l2+1)+n2) hstart hreturn
    refine ⟨((encode selector).length+1+(2*k+v+y+r+m+j+11))+((j2+1)+(l2+1)+n2),
      e,by omega,rfl,?_,?_⟩
    · simpa [e,cfg] using hmark
    · simpa only [selector,d,x,pos,u,out,e,Nat.add_assoc] using hall
  | succ w =>
    have hb : Holds t (a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+(r : Int)+4)
        (encode ((w+1)::vs) ++ [false,false]) := by simpa using bank
    obtain ⟨hbank,hframe,hstart⟩ := terminal_selector_to_bank t a k v y r w vs hl marker window extension hb
    let suffix := List.replicate w true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    let f := x+2+((suffix.length : Nat):Int)
    let out := spec (clearAt d t) f (suffix.length+2)
    have hbank' : Holds out x (encode (w::vs) ++ [true,false,false]) := hbank
    have hone : out x=true := bank_head out x w vs [true,false,false] hbank'
    let z' := min z (d-1)
    let b' := max b (f+1)
    have hd : d<x := by dsimp [x]; omega
    have hxf : x≤f := by dsimp [f]; omega
    have hleft : ∀ q, q≤z' → out q=false := by
      intro q hq
      have hqd : q<d := by dsimp [z'] at hq; omega
      have hqx : q<x := by omega
      have hh : out q=t q := hframe q (by omega) (Or.inl hqx)
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
    obtain ⟨m,j,l,n,final,hm,hn,hmark,_hprefix,hreturn⟩ :=
      state23_to83 (x-2) x z' b' out hleft hright (by omega) hone
    let e : Config 284 := cfg 83 (x-2-(m : Int)-(j : Int)-1) final
    have hall := segAdd machine _ _ _
      ((encode selector).length+1+(2*k+v+y+r+2*suffix.length+16))
      (m+(j+1)+(l+1)+n) hstart hreturn
    refine ⟨((encode selector).length+1+(2*k+v+y+r+2*suffix.length+16))+
      (m+(j+1)+(l+1)+n),e,by omega,rfl,?_,?_⟩
    · simpa [e,cfg] using hmark
    · simpa only [selector,d,x,suffix,f,out,e,Nat.add_assoc] using hall

#print axioms selector_roundtrip
#print axioms terminal_roundtrip
end Shared.Beeping.NPcoNP.NativeManySelectorRoundtrip
