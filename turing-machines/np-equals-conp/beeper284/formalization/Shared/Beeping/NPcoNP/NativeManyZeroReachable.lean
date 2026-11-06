import Shared.Beeping.NPcoNP.NativeManyZeroSelector
import Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport

/-! Blank-start finite support supplies the left-tail progress condition
for any reachable selector configuration satisfying the remaining layout. -/
namespace Shared.Beeping.NPcoNP.NativeManyZeroReachable
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeManyZeroSelector
open Shared.Beeping.NPcoNP.NativeManyZeroTail
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- Any left-zero tail yields an explicit natural-number distance bound
from the bank separator. -/
theorem tail_bound (t : Int → Bool) (x z : Int)
    (hz : ∀ q, q≤z → t q=false) :
    ∃ bound : Nat, ∀ q, q≤x-1-(bound : Int) → t q=false := by
  let bound := (x-1-min z (x-1)).toNat
  have hn : 0≤x-1-min z (x-1) := by omega
  have he : (bound : Int)=x-1-min z (x-1) := Int.toNat_of_nonneg hn
  refine ⟨bound,?_⟩
  intro q hq
  apply hz q
  rw [he] at hq
  omega

/-- At any actual finite blank-start visit to state 13 on a zero unary
block, the failure return reaches state 1 in finite silent time. -/
theorem reachable_zero_entry (time : Nat)
    (state : (machine.system.run time).state=13)
    (h0 : (machine.system.run time).tape (machine.system.run time).head=true)
    (h1 : (machine.system.run time).tape ((machine.system.run time).head+1)=false) :
    let t := (machine.system.run time).tape
    let x := (machine.system.run time).head
    ∃ bound m j : Nat, 0<m ∧ m≤bound+2 ∧ 0<j ∧ j≤bound+3 ∧
      let pos := x-1-(m : Int)
      let out := clearRange t (pos-(j : Int)+2) (pos+1)
      (∀ q, x-1≤q → out q=t q) ∧
      silentSegment machine (machine.system.run time) (cfg 1 (pos-(j : Int)) out) (3+m+j) := by
  dsimp only
  let t := (machine.system.run time).tape
  let x := (machine.system.run time).head
  obtain ⟨z,hz⟩ := run_has_left_zero time
  obtain ⟨bound,hbound⟩ := tail_bound t x z hz
  obtain ⟨m,j,hm,hmb,hj,hjb,hframe,hseg⟩ := zero_to1_left_tail x t bound h0 h1 hbound
  have hc : machine.system.run time = cfg 13 x t := by
    have hh : machine.system.run time =
        cfg (machine.system.run time).state (machine.system.run time).head (machine.system.run time).tape := by
      cases machine.system.run time
      rfl
    rw [state] at hh
    exact hh
  refine ⟨bound,m,j,hm,hmb,hj,hjb,hframe,?_⟩
  rw [hc]
  exact hseg

/-- At any actual finite blank-start time, the terminal selector's zero-bank
failure path progresses in finite silent time whenever its explicit window,
marker, continuation and bank layout hold. No left-tail hypothesis is added. -/
theorem reachable_terminal_zero (time : Nat) (a : Int) (k v y r : Nat) (vs : List Nat)
    (hl : (List.replicate k 0 ++ [v+3,y]).length=14)
    (state : (machine.system.run time).state=83)
    (head : (machine.system.run time).head =
      a+((encode (List.replicate k 0 ++ [v+3,y])).length : Int)-1)
    (marker : (machine.system.run time).tape (a-1)=true)
    (window : Holds (machine.system.run time).tape a
      (markerWindow (List.replicate k 0 ++ [v+3,y])))
    (extension : Holds (machine.system.run time).tape
      (a+((encode (List.replicate k 0 ++ [v+3,y])).length : Int))
      (List.replicate r true ++ [false]))
    (bank : Holds (machine.system.run time).tape
      (a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+(r : Int)+4)
      (encode (0::vs) ++ [false,false])) :
    let t := (machine.system.run time).tape
    let selector := List.replicate k 0 ++ [v+3,y]
    let d := a+((2*k : Nat):Int)+4
    let x := d+(v : Int)+(y : Int)+(r : Int)+4
    let u := clearAt d t
    ∃ bound m j : Nat, 0<m ∧ m≤bound+2 ∧ 0<j ∧ j≤bound+3 ∧
      let pos := x-1-(m : Int)
      let out := clearRange u (pos-(j : Int)+2) (pos+1)
      Holds out x (encode (0::vs) ++ [false,false]) ∧
      (∀ q, x-1≤q → out q=t q) ∧
      silentSegment machine (machine.system.run time) (cfg 1 (pos-(j : Int)) out)
        ((encode selector).length+1+(2*k+v+y+r+m+j+11)) := by
  dsimp only
  let t := (machine.system.run time).tape
  let selector := List.replicate k 0 ++ [v+3,y]
  let x := a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+(r : Int)+4
  obtain ⟨z,hz⟩ := run_has_left_zero time
  obtain ⟨bound,hbound⟩ := tail_bound t x z hz
  have htail : ∀ q, q≤a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+(r : Int)+3-(bound : Int) → t q=false := by
    intro q hq
    apply hbound q
    dsimp [x]
    omega
  obtain ⟨m,j,hm,hmb,hj,hjb,hres,hframe,hseg⟩ :=
    terminal_selector_zero_tail t a k v y r bound vs hl marker window extension bank htail
  have hc : machine.system.run time = cfg 83 (a+((encode selector).length : Int)-1) t := by
    have hh : machine.system.run time =
        cfg (machine.system.run time).state (machine.system.run time).head (machine.system.run time).tape := by
      cases machine.system.run time
      rfl
    rw [state,head] at hh
    exact hh
  refine ⟨bound,m,j,hm,hmb,hj,hjb,hres,hframe,?_⟩
  rw [hc]
  exact hseg

/-- The same finite-support discharge applies when the fourteen-block
window contains a complete next selector block. -/
theorem reachable_selector_zero (time : Nat) (a : Int) (k v y : Nat) (zs vs : List Nat)
    (hl : (List.replicate k 0 ++ (v+3)::y::0::zs).length=14)
    (state : (machine.system.run time).state=83)
    (head : (machine.system.run time).head =
      a+((encode (List.replicate k 0 ++ (v+3)::y::0::zs)).length : Int)-1)
    (marker : (machine.system.run time).tape (a-1)=true)
    (window : Holds (machine.system.run time).tape a
      (markerWindow (List.replicate k 0 ++ (v+3)::y::0::zs)))
    (bank : Holds (machine.system.run time).tape
      (a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+4)
      (encode (0::vs) ++ [false,false])) :
    let t := (machine.system.run time).tape
    let selector := List.replicate k 0 ++ (v+3)::y::0::zs
    let d := a+((2*k : Nat):Int)+4
    let x := d+(v : Int)+(y : Int)+4
    let u := clearAt d t
    ∃ bound m j : Nat, 0<m ∧ m≤bound+2 ∧ 0<j ∧ j≤bound+3 ∧
      let pos := x-1-(m : Int)
      let out := clearRange u (pos-(j : Int)+2) (pos+1)
      Holds out x (encode (0::vs) ++ [false,false]) ∧
      (∀ q, x-1≤q → out q=t q) ∧
      silentSegment machine (machine.system.run time) (cfg 1 (pos-(j : Int)) out)
        ((encode selector).length+1+(2*k+v+y+m+j+11)) := by
  dsimp only
  let t := (machine.system.run time).tape
  let selector := List.replicate k 0 ++ (v+3)::y::0::zs
  let x := a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+4
  obtain ⟨z,hz⟩ := run_has_left_zero time
  obtain ⟨bound,hbound⟩ := tail_bound t x z hz
  have htail : ∀ q, q≤a+((2*k : Nat):Int)+4+(v : Int)+(y : Int)+3-(bound : Int) → t q=false := by
    intro q hq
    apply hbound q
    dsimp [x]
    omega
  obtain ⟨m,j,hm,hmb,hj,hjb,hres,hframe,hseg⟩ :=
    selector_zero_tail t a k v y bound zs vs hl marker window bank htail
  have hc : machine.system.run time = cfg 83 (a+((encode selector).length : Int)-1) t := by
    have hh : machine.system.run time =
        cfg (machine.system.run time).state (machine.system.run time).head (machine.system.run time).tape := by
      cases machine.system.run time
      rfl
    rw [state,head] at hh
    exact hh
  refine ⟨bound,m,j,hm,hmb,hj,hjb,hres,hframe,?_⟩
  rw [hc]
  exact hseg

#print axioms reachable_zero_entry
#print axioms reachable_terminal_zero
#print axioms reachable_selector_zero
end Shared.Beeping.NPcoNP.NativeManyZeroReachable
