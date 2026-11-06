import Shared.Beeping.NPcoNP.NativeReturnPairBarrier
import Shared.Beeping.NPcoNP.NativeCarryReturn83

/-! Retain the complete tape effect and the two positive phases of the
state-23 return, for use in a recurring bank/control invariant. -/
namespace Shared.Beeping.NPcoNP.NativeReturnBelow83Exact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfMarkerRetain
open Shared.Beeping.NPcoNP.NativeReturnPairBarrier
open Shared.Beeping.NPcoNP.NativeCarryReturn83
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- A zero-pair barrier and a supplied right-hand one force the state-23
return. In addition to the two silent phases this records the entire output
as the actual carry, first-one clearing, and state-28 clearing operations.
The output agrees with the input strictly to the left of the new marker and
strictly right of both the original head and the clearing stop. A supplied
zero beyond the right-hand witness bounds the stop, so any later one is
preserved. -/
theorem state23_to83_below_exact (h d p z b : Int) (t : Int → Bool)
    (left : ∀ q, q ≤ z → t q = false) (right : ∀ q, b ≤ q → t q = false)
    (safe : ∀ q, d+2 ≤ q → q ≤ h → t q = false → t (q-1) = true)
    (hp : h ≤ p) (hone : t p = true) :
    ∃ (m j l n : Nat) (stop : Int) (out : Int → Bool),
      let h1 := h-(m : Int)
      let mark := h1-(j : Int)
      let scanHead := mark+1
      let u := put (result t h1 j) (scanHead+(l : Int)) false
      let head28 := scanHead+(l : Int)+1
      2≤m ∧ 0<n ∧ mark<d ∧ head28≤p+1 ∧ head28-1≤stop ∧
      out mark=true ∧ u (stop+1)=false ∧
      (∀ q, head28≤q → q≤stop → u q=true) ∧
      out=put (clearRange u head28 (stop+1)) stop true ∧
      (∀ q, q<mark → out q=t q) ∧
      (∀ q, h<q → stop<q → out q=t q) ∧
      (∀ q, h<q → p+1≤q → t q=false → stop<q) ∧
      (∀ q s, h<q → p+1≤q → t q=false → q<s → t s=true → out s=true) ∧
      silentSegment machine (cfg 23 h t) (cfg 1 h1 t) m ∧
      silentSegment machine (cfg 1 h1 t) (cfg 83 (mark-1) out) ((j+1)+(l+1)+n) := by
  obtain ⟨m,hm,hbelow,hscan⟩ := scan23_below h d z t left safe
  let h1 := h-(m : Int)
  have hpos : h1 < p := by dsimp [h1]; omega
  obtain ⟨j,l,n,stop,out,hn,hhead,hstop,hmark,hzero,hones,heq,hframe,hcarry⟩ :=
    carry_to83 h1 p z b t left right hpos hone
  let mark := h1-(j : Int)
  let scanHead := mark+1
  let u := put (result t h1 j) (scanHead+(l : Int)) false
  let head28 := scanHead+(l : Int)+1
  have hright : ∀ q, h<q → stop<q → out q=t q := by
    intro q hq hs
    have hqh1 : h1<q := by dsimp [h1]; omega
    have hqhit : q≠scanHead+(l : Int) := by omega
    have hclear : ¬ (head28≤q ∧ q<stop+1) := by omega
    rw [heq, put_other _ _ _ _ (show q≠stop by omega)]
    change (if head28≤q ∧ q<stop+1 then false else u q)=t q
    rw [if_neg hclear]
    change put (result t h1 j) (scanHead+(l : Int)) false q=t q
    rw [put_other _ _ _ _ hqhit]
    exact result_preserves_above t h1 q j hqh1
  have hlimit : ∀ q, h<q → p+1≤q → t q=false → stop<q := by
    intro q hq hpq hz
    have hqhead : head28≤q := by omega
    have hqh1 : h1<q := by dsimp [h1]; omega
    have hqhit : q≠scanHead+(l : Int) := by omega
    have hu : u q=t q := by
      change put (result t h1 j) (scanHead+(l : Int)) false q=t q
      rw [put_other _ _ _ _ hqhit]
      exact result_preserves_above t h1 q j hqh1
    by_contra hnstop
    have ho := hones q hqhead (by omega)
    change u q=true at ho
    rw [hu,hz] at ho
    contradiction
  have hmarker : ∀ q s, h<q → p+1≤q → t q=false → q<s → t s=true → out s=true := by
    intro q s hq hpq hz hqs ht
    rw [hright s (by omega) (by have := hlimit q hq hpq hz; omega)]
    exact ht
  refine ⟨m,j,l,n,stop,out,hm,hn,?_,hhead,hstop,hmark,hzero,hones,heq,hframe,hright,hlimit,hmarker,hscan,hcarry⟩
  omega

#print axioms state23_to83_below_exact
end Shared.Beeping.NPcoNP.NativeReturnBelow83Exact
