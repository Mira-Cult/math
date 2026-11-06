import Shared.Beeping.NPcoNP.NativeCarryReturn83
import Shared.Beeping.NPcoNP.NativeHalfState28Progress
import Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport

/-! Finite support supplies both blank tails on the actual run. A right-hand
one remains necessary and is not inferred from finite support. -/
namespace Shared.Beeping.NPcoNP.NativeCarryReachable83
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfMarkerRetain
open Shared.Beeping.NPcoNP.NativeCarryReturn83
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Every actual state-1 visit with a strictly rightward one returns to state
83 through a finite silent segment. The new marker and the left frame are
retained in the exact destination configuration. -/
theorem reachable_state1_to83 (time : Nat)
    (state : (machine.system.run time).state=1)
    (p : Int) (hp : (machine.system.run time).head<p)
    (hone : (machine.system.run time).tape p=true) :
    ∃ (j l n : Nat) (out : Int → Bool), 0<n ∧
      out ((machine.system.run time).head-(j : Int))=true ∧
      (∀ q, q<(machine.system.run time).head-(j : Int) → out q=(machine.system.run time).tape q) ∧
      silentSegment machine (machine.system.run time)
        (cfg 83 ((machine.system.run time).head-(j : Int)-1) out) ((j+1)+(l+1)+n) := by
  let c := machine.system.run time
  obtain ⟨z,hz⟩ := run_has_left_zero time
  obtain ⟨b,hb⟩ := run_has_right_zero time
  obtain ⟨j,l,n,stop,out,hn,_hhead,_hstop,hmark,_hz,_ho,_heq,hframe,hseg⟩ :=
    carry_to83 c.head p z b c.tape hz hb hp hone
  have hc : c=cfg 1 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    have hs : c.state=1 := state
    simpa only [hs] using he
  refine ⟨j,l,n,out,hn,hmark,hframe,?_⟩
  simpa only [← hc] using hseg

/-- A state-23 configuration with blank tails and a one at or to the right
of its head returns all the way to state 83, preserving the newly created
left marker. -/
theorem state23_to83 (h p z b : Int) (t : Int → Bool)
    (left : ∀ q, q≤z → t q=false) (right : ∀ q, b≤q → t q=false)
    (hp : h≤p) (hone : t p=true) :
    ∃ (m j l n : Nat) (out : Int → Bool), 0<m ∧ 0<n ∧
      let mark := h-(m : Int)-(j : Int)
      out mark=true ∧ (∀ q, q<mark → out q=t q) ∧
      silentSegment machine (cfg 23 h t) (cfg 83 (mark-1) out) (m+(j+1)+(l+1)+n) := by
  let k := (h-min z h).toNat
  have hk : h-(k : Int)≤z := by
    have hn : 0≤h-min z h := by omega
    have he : (k : Int)=h-min z h := Int.toNat_of_nonneg hn
    omega
  have ht : ∀ q≤h-(k : Int), t q=false := by intro q hq; exact left q (le_trans hq hk)
  obtain ⟨m,hm,_hbound,h23⟩ := scan_left_exact k h t ht false
  let h1 := h-(m : Int)
  have h23' : silentSegment machine (cfg 23 h t) (cfg 1 h1 t) m := by
    simpa [h1] using h23
  have hpos : h1<p := by dsimp [h1]; omega
  obtain ⟨j,l,n,stop,out,hn,_hhead,_hstop,hmark,_hz,_ho,_heq,hframe,hcarry⟩ :=
    carry_to83 h1 p z b t left right hpos hone
  have hall := segAdd machine _ _ _ m ((j+1)+(l+1)+n) h23' hcarry
  refine ⟨m,j,l,n,out,hm,hn,?_,?_,?_⟩
  · simpa [h1] using hmark
  · simpa [h1] using hframe
  · simpa [h1,Nat.add_assoc] using hall

/-- Blank-start finite support supplies both tails at every finite state-23
visit. A rightward one is still an explicit physical invariant. -/
theorem reachable_state23_to83 (time : Nat)
    (state : (machine.system.run time).state=23)
    (p : Int) (hp : (machine.system.run time).head≤p)
    (hone : (machine.system.run time).tape p=true) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=83 ∧ e.tape (e.head+1)=true ∧
      silentSegment machine (machine.system.run time) e n := by
  let c := machine.system.run time
  obtain ⟨z,hz⟩ := run_has_left_zero time
  obtain ⟨b,hb⟩ := run_has_right_zero time
  obtain ⟨m,j,l,n,out,hm,hn,hmark,_hframe,hseg⟩ :=
    state23_to83 c.head p z b c.tape hz hb hp hone
  let mark := c.head-(m : Int)-(j : Int)
  let e : Config 284 := cfg 83 (mark-1) out
  have hc : c=cfg 23 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    have hs : c.state=23 := state
    simpa only [hs] using he
  refine ⟨m+(j+1)+(l+1)+n,e,by omega,rfl,?_,?_⟩
  · simpa [e,cfg,mark] using hmark
  · simpa only [← hc,e,mark] using hseg

#print axioms reachable_state1_to83
#print axioms state23_to83
#print axioms reachable_state23_to83
end Shared.Beeping.NPcoNP.NativeCarryReachable83
