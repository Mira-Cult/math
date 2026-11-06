import Shared.Beeping.NPcoNP.NativeManyZeroDispatch
import Shared.Beeping.NPcoNP.NativeManyWindowBank
import Shared.Beeping.NPcoNP.NativeManyTerminalWindow

/-! Positive selector control can select a zero-valued following bank.
A finite left-blank tail gives paid progress through the failure return. -/
namespace Shared.Beeping.NPcoNP.NativeManyZeroSelector
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeHalfMarkerMany
open Shared.Beeping.NPcoNP.NativeManyWindowBank
open Shared.Beeping.NPcoNP.NativeManyTerminalWindow
open Shared.Beeping.NPcoNP.NativeManyZeroDispatch
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- Ordinary fourteen-block window, zero-valued following bank, and a
left-blank tail: the selected failure branch reaches state 1 in finite
silent time without changing the bank. -/
theorem selector_zero_tail (t : Int → Bool) (a : Int) (k v y bound : Nat) (zs vs : List Nat)
    (hl : (List.replicate k 0 ++ (v+3)::y::0::zs).length=14)
    (marker : t (a-1)=true)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ (v+3)::y::0::zs)))
    (bank : Holds t (a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+4)
      (encode (0::vs) ++ [false,false]))
    (tail : ∀ q, q≤a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+3-(bound : Int) → t q=false) :
    let selector := List.replicate k 0 ++ (v+3)::y::0::zs
    let d := a+((2*k : Nat):Int)+4
    let x := d+(v : Int)+(y : Int)+4
    let u := clearAt d t
    ∃ m j : Nat, 0<m ∧ m≤bound+2 ∧ 0<j ∧ j≤bound+3 ∧
      let pos := x-1-(m : Int)
      let out := clearRange u (pos-(j : Int)+2) (pos+1)
      Holds out x (encode (0::vs) ++ [false,false]) ∧
      (∀ z, x-1≤z → out z=t z) ∧
      silentSegment machine (cfg 83 (a+((encode selector).length : Int)-1) t)
        (cfg 1 (pos-(j : Int)) out)
        ((encode selector).length+1+(2*k+v+y+m+j+11)) := by
  dsimp only
  let selector := List.replicate k 0 ++ (v+3)::y::0::zs
  let d := a+((2*k : Nat):Int)+4
  let x := d+(v : Int)+(y : Int)+4
  let u := clearAt d t
  have hentry := marker_window_to93 t a selector hl window marker
  have hhead : t d=true := many_marker_head t a k v y 0 zs window
  obtain ⟨hfirst,hsecond⟩ := many_scan_words t a k v y 0 zs window
  have he : d+(v : Int)+((y+1 : Nat):Int)+3=x := by dsimp [x]; push_cast; omega
  have hbank : Holds t (d+(v : Int)+((y+1 : Nat):Int)+3)
      (encode (0::vs) ++ [false,false]) := by rw [he]; exact bank
  have htail : ∀ q, q≤d+(v : Int)+((y+1 : Nat):Int)+2-(bound : Int) → t q=false := by
    intro q hq
    apply tail q
    dsimp [d] at hq
    push_cast at hq
    omega
  obtain ⟨m,j,hm,hmb,hj,hjb,hres,hframe,hdispatch⟩ :=
    dispatch260_zero_tail v (y+1) bound vs d t hhead hfirst hsecond hbank htail
  rw [he] at hres hframe hdispatch
  have hw : Holds t a (markerWindow (List.replicate k 0 ++ ((v+1)+2)::y::0::zs)) := by
    simpa [Nat.add_assoc] using window
  have hscan := marker_window_to_ge_two t a k (v+1) (y::0::zs) (by simp) hw
  have hbody := segAdd machine _ _ _ (2*k+4) (v+(y+1)+m+j+6) hscan hdispatch
  have hc : 2*k+4+(v+(y+1)+m+j+6)=2*k+v+y+m+j+11 := by omega
  rw [hc] at hbody
  have hall := segAdd machine _ _ _ ((encode selector).length+1)
    (2*k+v+y+m+j+11) hentry hbody
  exact ⟨m,j,hm,hmb,hj,hjb,hres,hframe,hall⟩

/-- Terminal-window counterpart: the second scan may extend beyond the
last selector block, but its finite continuation and delimiter are explicit. -/
theorem terminal_selector_zero_tail (t : Int → Bool) (a : Int) (k v y r bound : Nat) (vs : List Nat)
    (hl : (List.replicate k 0 ++ [v+3,y]).length=14)
    (marker : t (a-1)=true)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ [v+3,y])))
    (extension : Holds t (a+((encode (List.replicate k 0 ++ [v+3,y])).length : Int))
      (List.replicate r true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+(r : Int)+4)
      (encode (0::vs) ++ [false,false]))
    (tail : ∀ q, q≤a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+(r : Int)+3-(bound : Int) → t q=false) :
    let selector := List.replicate k 0 ++ [v+3,y]
    let d := a+((2*k : Nat):Int)+4
    let x := d+(v : Int)+(y : Int)+(r : Int)+4
    let u := clearAt d t
    ∃ m j : Nat, 0<m ∧ m≤bound+2 ∧ 0<j ∧ j≤bound+3 ∧
      let pos := x-1-(m : Int)
      let out := clearRange u (pos-(j : Int)+2) (pos+1)
      Holds out x (encode (0::vs) ++ [false,false]) ∧
      (∀ z, x-1≤z → out z=t z) ∧
      silentSegment machine (cfg 83 (a+((encode selector).length : Int)-1) t)
        (cfg 1 (pos-(j : Int)) out)
        ((encode selector).length+1+(2*k+v+y+r+m+j+11)) := by
  dsimp only
  let selector := List.replicate k 0 ++ [v+3,y]
  let d := a+((2*k : Nat):Int)+4
  let x := d+(v : Int)+(y : Int)+(r : Int)+4
  let u := clearAt d t
  have hentry := marker_window_to93 t a selector hl window marker
  obtain ⟨hhead,hfirst,hsecond⟩ := terminal_scan_words t a k v y r window extension
  have he : d+(v : Int)+((y+1+r : Nat):Int)+3=x := by dsimp [x]; push_cast; omega
  have hbank : Holds t (d+(v : Int)+((y+1+r : Nat):Int)+3)
      (encode (0::vs) ++ [false,false]) := by rw [he]; exact bank
  have htail : ∀ q, q≤d+(v : Int)+((y+1+r : Nat):Int)+2-(bound : Int) → t q=false := by
    intro q hq
    apply tail q
    dsimp [d] at hq
    push_cast at hq
    omega
  obtain ⟨m,j,hm,hmb,hj,hjb,hres,hframe,hdispatch⟩ :=
    dispatch260_zero_tail v (y+1+r) bound vs d t hhead hfirst hsecond hbank htail
  rw [he] at hres hframe hdispatch
  have hw : Holds t a (markerWindow (List.replicate k 0 ++ ((v+1)+2)::[y])) := by
    simpa [Nat.add_assoc] using window
  have hscan := marker_window_to_ge_two t a k (v+1) [y] (by simp) hw
  have hbody := segAdd machine _ _ _ (2*k+4) (v+(y+1+r)+m+j+6) hscan hdispatch
  have hc : 2*k+4+(v+(y+1+r)+m+j+6)=2*k+v+y+r+m+j+11 := by omega
  rw [hc] at hbody
  have hall := segAdd machine _ _ _ ((encode selector).length+1)
    (2*k+v+y+r+m+j+11) hentry hbody
  exact ⟨m,j,hm,hmb,hj,hjb,hres,hframe,hall⟩

#print axioms selector_zero_tail
#print axioms terminal_selector_zero_tail
end Shared.Beeping.NPcoNP.NativeManyZeroSelector
