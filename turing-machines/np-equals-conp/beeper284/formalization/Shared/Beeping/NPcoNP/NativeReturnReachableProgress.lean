import Shared.Beeping.NPcoNP.NativeReturnMarkerInvariant
import Shared.Beeping.NPcoNP.NativeState28MarkerScan
import Shared.Beeping.NPcoNP.NativeIncMarkerProgress

/-! Unconditional progress for actual blank-start returns through state 28.
The separate all-zero supplied state-28 trap remains valid but is unreachable. -/
namespace Shared.Beeping.NPcoNP.NativeReturnReachableProgress
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exit
open Shared.Beeping.NPcoNP.NativeHalfState97Progress
open Shared.Beeping.NPcoNP.NativeReturnMarkerInvariant
open Shared.Beeping.NPcoNP.NativeState28MarkerScan
open Shared.Beeping.NPcoNP.NativeIncMarkerProgress
open Shared.Beeping.NPcoNP.NativeHalfState12Progress
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

/-- The finite-support all-zero state-28 trap is not on the blank-start run. -/
theorem blank28_unreachable (time : Nat) (h : Int) :
    machine.system.run time ≠ cfg 28 h (fun _ => false) := by
  intro he
  have hs : (machine.system.run time).state=28 := by rw [he]; rfl
  obtain ⟨p,_,hm⟩ := (run_invariant time).2 hs
  rw [he] at hm
  simp [cfg] at hm

/-- Every actual state-28 visit silently reaches state 83. The marker is
proved by induction on the literal blank-start run, not assumed. -/
theorem reachable_28_to_83 (time : Nat)
    (hstate : (machine.system.run time).state=28) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=83 ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨p,hp,hm⟩ := (run_invariant time).2 hstate
  obtain ⟨b,hb⟩ := run_has_right_zero time
  let h := (machine.system.run time).head
  let tape := (machine.system.run time).tape
  let k := (max b h-h).toNat
  have hk : b ≤ h+(k : Int) := by
    have hn : 0≤max b h-h := by omega
    have he : (k : Int)=max b h-h := Int.toNat_of_nonneg hn
    omega
  have hz : tape (h+(k : Int))=false := hb _ hk
  have hl : tape (h-1)=false := reachable_28_left_zero time hstate
  obtain ⟨n,c,hn,_,hc,ht,hpos,hmark,hscan⟩ :=
    scan_to_zero_with_marker k h p tape hl hz hp hm
  let e97 : Config 284 := cfg 97 (c.head-1) (put c.tape c.head true)
  have hc6 : c=cfg 6 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    simpa only [hc] using he
  have hstep : machine.step c=(e97,false) := by
    conv_lhs => rw [hc6]
    exact step6_zero c.head c.tape ht
  have hp97 : p≤e97.head := by dsimp [e97,cfg]; omega
  have hm97 : e97.tape p=true := by
    change put c.tape c.head true p=true
    rw [put_other _ _ _ _ (by omega)]
    exact hmark
  let d := (e97.head-p).toNat
  have hd : e97.head-(d : Int)=p := by
    have hn' : 0≤e97.head-p := by omega
    have he : (d : Int)=e97.head-p := Int.toNat_of_nonneg hn'
    omega
  have hone : e97.tape (e97.head-(d : Int))=true := by rw [hd]; exact hm97
  obtain ⟨m,hm',_,hmore⟩ := scan_to_one d e97.head e97.tape hone
  let e83 : Config 284 := cfg 83 (e97.head-(m : Int)) e97.tape
  have hcfg : machine.system.run time=cfg 28 h tape := by
    cases hc' : machine.system.run time with
    | mk state head cells =>
      simp only [hc',cfg] at hstate ⊢
      simp only [h,tape,hc',cfg] at *
      cases hstate
      rfl
  have hscan' : silentSegment machine (machine.system.run time) c n := by
    rw [hcfg]
    exact hscan
  have hmore' : silentSegment machine e97 e83 m := by
    have he : e97=cfg 97 e97.head e97.tape := by rfl
    rw [he]
    exact hmore
  refine ⟨n+1+m,e83,by omega,rfl,?_⟩
  exact segAdd machine _ _ _ (n+1) m
    (segAdd machine _ _ _ n 1 hscan' (oneSeg machine _ _ hstep)) hmore'

/-- The 14/22 loop and its marked return reach the selector entry on every
actual state-14 visit. -/
theorem reachable_14_to_83 (time : Nat)
    (hstate : (machine.system.run time).state=14) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=83 ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨n,c,hn,hc,hseg⟩ := reachable_14_to_28 time hstate
  have hrun : machine.system.run (time+n)=c := by
    rw [EventSystem.run_add, ← ScalarWordRefinement.advance_ofBeep]
    exact hseg.1
  have h28 : (machine.system.run (time+n)).state=28 := by rw [hrun]; exact hc
  obtain ⟨m,e,hm,he,hmore⟩ := reachable_28_to_83 (time+n) h28
  refine ⟨n+m,e,by omega,he,?_⟩
  apply segAdd machine _ _ _ n m hseg
  rw [← hrun]
  exact hmore

/-- The state-261 one-branch reaches the selector entry without any marker
premise, whenever this branch occurs on the actual blank-start run. -/
theorem reachable_261_one_to_83 (time : Nat)
    (hstate : (machine.system.run time).state=261)
    (hone : (machine.system.run time).tape (machine.system.run time).head=true) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=83 ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨n,c,hn,hc,hseg⟩ := reachable_261_one_to_14 time hstate hone
  have hrun : machine.system.run (time+n)=c := by
    rw [EventSystem.run_add, ← ScalarWordRefinement.advance_ofBeep]
    exact hseg.1
  have h14 : (machine.system.run (time+n)).state=14 := by rw [hrun]; exact hc
  obtain ⟨m,e,hm,he,hmore⟩ := reachable_14_to_83 (time+n) h14
  refine ⟨n+m,e,by omega,he,?_⟩
  apply segAdd machine _ _ _ n m hseg
  rw [← hrun]
  exact hmore

#print axioms blank28_unreachable
#print axioms reachable_28_to_83
#print axioms reachable_14_to_83
#print axioms reachable_261_one_to_83
end Shared.Beeping.NPcoNP.NativeReturnReachableProgress
