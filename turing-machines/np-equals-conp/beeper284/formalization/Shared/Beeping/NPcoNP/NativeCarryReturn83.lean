import Shared.Beeping.NPcoNP.NativeCarryMarker28
import Shared.Beeping.NPcoNP.NativeHalfMarkerExact

/-! A protected right-hand one prevents state-27 stall. The state-1 carry
creates the left marker used by state 97 to return to state 83. -/
namespace Shared.Beeping.NPcoNP.NativeCarryReturn83
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfMarkerExact
open Shared.Beeping.NPcoNP.NativeCarryMarker28
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- A left blank tail, a right blank tail, and a one strictly right of the
state-1 head force a finite silent return to state 83. The marker location,
complete output tape and protected left prefix are explicit. -/
theorem carry_to83 (h p z b : Int) (t : Int → Bool)
    (left : ∀ q, q≤z → t q=false) (right : ∀ q, b≤q → t q=false)
    (hp : h<p) (hone : t p=true) :
    ∃ (j l n : Nat) (stop : Int) (out : Int → Bool), 0<n ∧
      let mark := h-(j : Int)
      let scanHead := mark+1
      let u := put (result t h j) (scanHead+(l : Int)) false
      let head28 := scanHead+(l : Int)+1
      head28≤p+1 ∧ head28-1≤stop ∧ out mark=true ∧
      u (stop+1)=false ∧ (∀ q, head28≤q → q≤stop → u q=true) ∧
      out=put (clearRange u head28 (stop+1)) stop true ∧
      (∀ q, q<mark → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 83 (mark-1) out) ((j+1)+(l+1)+n) := by
  obtain ⟨j,l,hmarkle,hheadle,hmark,hcorr,hframe,hleft,hcarry⟩ := carry_to28 h p z t left hp hone
  let mark := h-(j : Int)
  let scanHead := mark+1
  let u := put (result t h j) (scanHead+(l : Int)) false
  let head28 := scanHead+(l : Int)+1
  let top := max b (max (h+1) head28)
  let r := (top-head28).toNat
  have htop : head28≤top := by dsimp [top]; omega
  have hr : (r : Int)=top-head28 := Int.toNat_of_nonneg (by omega)
  have hpos : head28+(r : Int)=top := by omega
  have hz : u (head28+(r : Int))=false := by
    rw [hpos]
    have hh : u top=t top := hframe top (by dsimp [top]; omega) htop
    rw [hh]
    exact right top (by dsimp [top]; omega)
  have hp' : mark≤head28-2 := by dsimp [head28,scanHead]; omega
  obtain ⟨n,stop,out,hn,hstop,hmarkout,hzero,hones,heq,hpres,hreturn⟩ :=
    state28_to83_exact head28 mark u hp' hmark hcorr r hz
  have houtleft : ∀ q, q<mark → out q=t q := by
    intro q hq
    calc
      out q = u q := hpres q (by omega)
      _ = t q := hleft q hq
  refine ⟨j,l,n,stop,out,hn,hheadle,hstop,hmarkout,hzero,hones,heq,houtleft,?_⟩
  exact segAdd machine _ _ _ ((j+1)+(l+1)) n hcarry hreturn

#print axioms carry_to83
end Shared.Beeping.NPcoNP.NativeCarryReturn83
