import Shared.Beeping.NPcoNP.Table284Flags
import Shared.Beeping.NPcoNP.NativeHalfEntryTo28
import Shared.Beeping.NPcoNP.NativeCarryMarker28
import Shared.Beeping.NPcoNP.NativeHalfState27Trap

/-! The literal marked transition and its paid state-1 carry/dispatch.
These are supplied-configuration results, not blank-start reachability or
a completed graph-to-table simulation. -/
namespace Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfEntryTo28
open Shared.Beeping.NPcoNP.NativeCarryMarker28
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfState1FiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfState27Trap
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

abbrev physical := machineWordSystem machine (BitLabels.fromFlags machine)

/-- The fixed marked row clears the current one, moves left, and emits. -/
theorem step99_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 99 h t) = (cfg 1 (h-1) (put t h false),true) := by
  change machine.step ⟨99,h,t⟩ = (⟨1,h-1,put t h false⟩,true)
  have hw : (⟨99,h,t⟩ : Config 284).write false = put t h false := rfl
  have hr : machine.table.row (99 : Fin 284) true = ⟨false,.left,1,true⟩ := by decide
  simp [Machine.step,ht,hr,Move.apply,hw]

/-- Prefix any proved silent continuation by the physical flagged transition.
The complete ordered Boolean output is exactly one `true`. -/
theorem beep_then_silent (h : Int) (t : Int → Bool) (ht : t h=true)
    (n : Nat) (e : Config 284)
    (hseg : silentSegment machine (cfg 1 (h-1) (put t h false)) e n) :
    physical.advance (cfg 99 h t) (1+n)=e ∧
    physical.wordFrom (cfg 99 h t) (1+n)=[true] := by
  have hs : (W machine).step (cfg 99 h t) =
      (cfg 1 (h-1) (put t h false),[()]) := by
    simp [W,WordEventSystem.ofBeep,Machine.system,step99_one h t ht]
  have ha : (W machine).advance (cfg 99 h t) (1+n)=e := by
    rw [WordEventSystem.advance_add]
    simpa [WordEventSystem.advance,hs] using hseg.1
  have hw : (W machine).wordFrom (cfg 99 h t) (1+n)=[()] := by
    rw [WordEventSystem.wordFrom_add]
    simp [WordEventSystem.wordFrom,WordEventSystem.advance,hs,hseg.2]
  change (machineWordSystem machine (BitLabels.fromFlags machine)).advance _ _ = _ ∧
    (machineWordSystem machine (BitLabels.fromFlags machine)).wordFrom _ _ = _
  rw [← ScalarWordRefinement.beepBits_machine]
  constructor
  · simpa [ScalarWordRefinement.beepBits,WordEventSystem.map_advance,W] using ha
  · unfold ScalarWordRefinement.beepBits
    rw [WordEventSystem.map_wordFrom]
    change ((W machine).wordFrom (cfg 99 h t) (1+n)).map (fun _ => true) = [true]
    rw [hw]
    rfl

/-- A marked transition followed by a carry across exactly `k` ones costs
`k+2` transitions and emits precisely the marked event. The entire tape
after both operations is given explicitly. -/
theorem beep_then_carry (h : Int) (t : Int → Bool) (k : Nat)
    (ht : t h=true)
    (hcarry : downHolds t (h-1) (List.replicate k true ++ [false])) :
    let u := put t h false
    physical.advance (cfg 99 h t) (k+2) =
      cfg 27 (h-1-(k : Int)+1) (result u (h-1) k) ∧
    physical.wordFrom (cfg 99 h t) (k+2)=[true] := by
  dsimp only
  have hc : downHolds (put t h false) (h-1) (List.replicate k true ++ [false]) :=
    downHolds_put t (h-1) h _ false (by omega) hcarry
  have hs := NativeHalfState1Scan.scan (put t h false) (h-1) k hc
  have he := beep_then_silent h t ht (k+1) _ hs
  simpa only [show 1+(k+1)=k+2 by omega] using he

/-- A marked row followed by a finite left carry and a bounded zero corridor
reaches state 28 with the exact resulting tape and exactly one event. The
left-zero tail, cleared corridor, and first bank one are explicit invariants. -/
theorem beep_to28 (h ctrl z : Int) (t : Int → Bool)
    (ht : t h=true) (hh : h-1<ctrl) (hzpos : z<h)
    (hz : ∀ p≤z, t p=false)
    (hzeros : ∀ p, h+1≤p → p≤ctrl+1 → t p=false)
    (hone : t (ctrl+2)=true) :
    let u := put t h false
    ∃ (n k : Nat), 1<n ∧
      downHolds u (h-1) (List.replicate k true ++ [false]) ∧
      physical.advance (cfg 99 h t) n =
        cfg 28 (ctrl+3) (put (result u (h-1) k) (ctrl+2) false) ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  dsimp only
  let u := put t h false
  have hz' : ∀ p≤z, u p=false := by
    intro p hp
    change put t h false p=false
    rw [put_other t h p false (by omega)]
    exact hz p hp
  have hzeros' : ∀ p, (h-1)+1≤p → p≤ctrl+1 → u p=false := by
    intro p hp hp'
    by_cases he : p=h
    · simp [u,put,he]
    · change put t h false p=false
      rw [put_other t h p false he]
      exact hzeros p (by omega) hp'
  have hone' : u (ctrl+2)=true := by
    change put t h false (ctrl+2)=true
    rw [put_other t h (ctrl+2) false (by omega)]
    exact hone
  obtain ⟨n,k,hn,hcarry,hseg⟩ := state1_header_dispatch u (h-1) ctrl z hh hz' hzeros' hone'
  obtain ⟨ha,hw⟩ := beep_then_silent h t ht n _ hseg
  exact ⟨1+n,k,by omega,hcarry,ha,hw⟩

/-- A left-zero tail and any one strictly right of the flagged head suffice:
the machine emits once, completes the carry, and reaches state 28 with a
new left marker and an empty corridor. No initial zero corridor is assumed. -/
theorem beep_to28_with_marker (h p z : Int) (t : Int → Bool)
    (ht : t h=true) (hzpos : z<h) (left : ∀ q≤z, t q=false)
    (hp : h<p) (hone : t p=true) :
    ∃ (n : Nat) (mark : Int) (e : Config 284), 1<n ∧ e.state=28 ∧
      mark<e.head ∧ e.head≤p+1 ∧ e.tape mark=true ∧
      (∀ q, mark<q → q<e.head → e.tape q=false) ∧
      physical.advance (cfg 99 h t) n=e ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  let u := put t h false
  have hleft : ∀ q≤z, u q=false := by
    intro q hq
    change put t h false q=false
    rw [put_other t h q false (by omega)]
    exact left q hq
  have hright : u p=true := by
    change put t h false p=true
    rw [put_other t h p false (by omega)]
    exact hone
  obtain ⟨j,l,_hmarkbound,hheadbound,hmark,hcorr,_hframe,_hleftframe,hseg⟩ :=
    carry_to28 (h-1) p z u hleft (by omega) hright
  let mark := h-1-(j : Int)
  let scanHead := mark+1
  let out := put (result u (h-1) j) (scanHead+(l : Int)) false
  let head28 := scanHead+(l : Int)+1
  have hh : mark<head28 := by dsimp [mark,scanHead,head28]; omega
  obtain ⟨ha,hw⟩ := beep_then_silent h t ht ((j+1)+(l+1)) _ hseg
  exact ⟨1+((j+1)+(l+1)),mark,cfg 28 head28 out,by omega,rfl,hh,hheadbound,
    hmark,hcorr,ha,hw⟩

/-- At any actual blank-start beep, finite support supplies the left-zero
tail automatically. A one to the right then forces an exact-one-event finite
segment to state 28. Reachability of such a right marker is not assumed away. -/
theorem reachable_beep_to28 (time : Nat) (hb : machine.system.BeepAt time)
    (p : Int) (hp : (machine.system.run time).head<p)
    (hone : (machine.system.run time).tape p=true) :
    ∃ (n : Nat) (mark : Int) (e : Config 284), 1<n ∧ e.state=28 ∧
      mark<e.head ∧ e.head≤p+1 ∧ e.tape mark=true ∧
      (∀ q, mark<q → q<e.head → e.tape q=false) ∧
      physical.advance (machine.system.run time) n=e ∧
      physical.wordFrom (machine.system.run time) n=[true] := by
  let c := machine.system.run time
  have hs : c.state.val=99 ∧ c.tape c.head=true := (beepAt_iff time).mp hb
  have hc : c=cfg 99 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    have hstate : c.state=(99 : Fin 284) := Fin.ext hs.1
    simpa only [hstate] using he
  obtain ⟨b,hb⟩ := run_has_left_zero time
  let z := min b (c.head-1)
  have hz : ∀ q≤z, c.tape q=false := by
    intro q hq
    exact hb q (le_trans hq (min_le_left _ _))
  obtain ⟨n,mark,e,hn,hstate,hmark,hp',hbit,hcorr,ha,hw⟩ :=
    beep_to28_with_marker c.head p z c.tape hs.2 (by dsimp [z]; omega) hz hp hone
  refine ⟨n,mark,e,hn,hstate,hmark,hp',hbit,hcorr,?_,?_⟩
  · simpa only [←hc] using ha
  · simpa only [←hc] using hw

/-- With no right-hand one, the marked step and finite left carry finish,
but state 27 scans a zero ray forever without another beep. This is a real
alternative to progress, not a claim that the layout is reachable. -/
theorem beep_without_right_marker (h z : Int) (t : Int → Bool)
    (ht : t h=true) (left : ∀ q≤z, t q=false)
    (right : ∀ q, h<q → t q=false) :
    ∃ (k : Nat),
      let u := put t h false
      let out := result u (h-1) k
      let scanHead := h-1-(k : Int)+1
      physical.advance (cfg 99 h t) (k+2)=cfg 27 scanHead out ∧
      physical.wordFrom (cfg 99 h t) (k+2)=[true] ∧
      ∀ j : Nat, (machine.system.advance (cfg 27 scanHead out) j).state=27 ∧
        ¬ machine.system.BeepFrom (cfg 27 scanHead out) j := by
  let d := (h-1-min z (h-1)).toNat
  have hd : h-1-(d : Int)≤z := by
    have he : (d : Int)=h-1-min z (h-1) := Int.toNat_of_nonneg (by omega)
    omega
  obtain ⟨k,_hk,hcarry⟩ := first_zero d (h-1) t (left _ hd)
  let u := put t h false
  let out := result u (h-1) k
  let a := h-1-(k : Int)+1
  have hzero : ∀ i : Nat, out (a+(i : Int))=false := by
    intro i
    let q := a+(i : Int)
    have hq : h-1-(k : Int)<q := by dsimp [q,a]; omega
    have hne : q≠h-1-(k : Int) := by omega
    change result u (h-1) k q=false
    rw [result,put_other _ _ _ _ hne]
    by_cases hbound : q≤h-1
    · change (if h-1-(k : Int)<q ∧ q≤h-1 then false else u q)=false
      rw [if_pos (And.intro hq hbound)]
    · have hu : u q=false := by
        by_cases he : q=h
        · simp [u,put,he]
        · change put t h false q=false
          rw [put_other t h q false he]
          exact right q (by omega)
      simp [cleared,hbound,hu]
  obtain ⟨ha,hw⟩ := beep_then_carry h t k ht hcarry
  refine ⟨k,ha,hw,?_⟩
  intro j
  constructor
  · rw [run_zeroes a out hzero j]
    rfl
  · exact run_zeroes_silent a out hzero j

/-- At every reachable beep, either a right marker yields finite progress to
state 28 or the paid carry reaches an eternally silent state-27 scan. This
does not prove which alternative the blank-start run actually takes. -/
theorem reachable_beep_progress_or_stall (time : Nat)
    (hb : machine.system.BeepAt time) :
    (∃ (n : Nat) (e : Config 284), 1<n ∧ e.state=28 ∧
      physical.advance (machine.system.run time) n=e ∧
      physical.wordFrom (machine.system.run time) n=[true]) ∨
    (∃ (n : Nat) (e : Config 284), 1<n ∧ e.state=27 ∧
      physical.advance (machine.system.run time) n=e ∧
      physical.wordFrom (machine.system.run time) n=[true] ∧
      ∀ j : Nat, (machine.system.advance e j).state=27 ∧
        ¬ machine.system.BeepFrom e j) := by
  let c := machine.system.run time
  have hs : c.state.val=99 ∧ c.tape c.head=true := (beepAt_iff time).mp hb
  have hc : c=cfg 99 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    have hstate : c.state=(99 : Fin 284) := Fin.ext hs.1
    simpa only [hstate] using he
  by_cases hr : ∃ p : Int, c.head<p ∧ c.tape p=true
  · obtain ⟨p,hp,hone⟩ := hr
    obtain ⟨n,_mark,e,hn,he,_hmark,_hbound,_hbit,_hcorr,ha,hw⟩ :=
      reachable_beep_to28 time hb p hp hone
    exact Or.inl ⟨n,e,hn,he,ha,hw⟩
  · obtain ⟨b,hb⟩ := run_has_left_zero time
    let z := min b (c.head-1)
    have hz : ∀ q≤z, c.tape q=false := by
      intro q hq
      exact hb q (le_trans hq (min_le_left _ _))
    have hright : ∀ q, c.head<q → c.tape q=false := by
      intro q hq
      cases hqv : c.tape q with
      | false => rfl
      | true => exact False.elim (hr ⟨q,hq,hqv⟩)
    obtain ⟨k,ha,hw,htrap⟩ :=
      beep_without_right_marker c.head z c.tape hs.2 hz hright
    let e : Config 284 := cfg 27 (c.head-1-(k : Int)+1) (result (put c.tape c.head false) (c.head-1) k)
    refine Or.inr ⟨k+2,e,by omega,rfl,?_,?_,htrap⟩
    · simpa only [←hc] using ha
    · simpa only [←hc] using hw

/-- If a reachable flagged transition has no one to its right, it is the
last beep: after a finite carry, the machine scans zeros silently forever. -/
theorem reachable_beep_without_marker_eventually_silent (time : Nat)
    (hb : machine.system.BeepAt time)
    (right : ∀ q, (machine.system.run time).head<q →
      (machine.system.run time).tape q=false) :
    machine.system.EventuallySilent := by
  let c := machine.system.run time
  have hs : c.state.val=99 ∧ c.tape c.head=true := (beepAt_iff time).mp hb
  have hc : c=cfg 99 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    have hstate : c.state=(99 : Fin 284) := Fin.ext hs.1
    simpa only [hstate] using he
  obtain ⟨b,hb⟩ := run_has_left_zero time
  have hz : ∀ q≤b, c.tape q=false := hb
  obtain ⟨k,ha,_hw,htrap⟩ := beep_without_right_marker c.head b c.tape hs.2 hz right
  let e : Config 284 := cfg 27 (c.head-1-(k : Int)+1)
    (result (put c.tape c.head false) (c.head-1) k)
  have ha' : machine.system.advance c (k+2)=e := by
    rw [←hc] at ha
    change (machineWordSystem machine (BitLabels.fromFlags machine)).advance c (k+2)=e at ha
    rw [← ScalarWordRefinement.beepBits_machine] at ha
    simpa [ScalarWordRefinement.beepBits,ScalarWordRefinement.advance_ofBeep] using ha
  refine ⟨time+(k+2),?_⟩
  intro m hm
  let j := m-(time+(k+2))
  have he : m=(time+(k+2))+j := by dsimp [j]; omega
  rw [he,EventSystem.beepAt_add_iff,EventSystem.run_add,ha']
  exact (htrap j).2

/-- On any run that is not eventually silent, every actual beep has a
right-hand marker and therefore satisfies the progress premise above. -/
theorem nonsilent_beep_has_right_marker (h : ¬ machine.system.EventuallySilent)
    (time : Nat) (hb : machine.system.BeepAt time) :
    ∃ p : Int, (machine.system.run time).head<p ∧
      (machine.system.run time).tape p=true := by
  by_contra hn
  apply h
  apply reachable_beep_without_marker_eventually_silent time hb
  intro q hq
  cases hv : (machine.system.run time).tape q with
  | false => rfl
  | true => exact False.elim (hn ⟨q,hq,hv⟩)

#print axioms step99_one
#print axioms beep_then_silent
#print axioms beep_then_carry
#print axioms beep_to28
#print axioms beep_to28_with_marker
#print axioms reachable_beep_to28
#print axioms beep_without_right_marker
#print axioms reachable_beep_progress_or_stall
#print axioms reachable_beep_without_marker_eventually_silent
#print axioms nonsilent_beep_has_right_marker
end Shared.Beeping.NPcoNP.NativeBeepCarry
