import Shared.Beeping.NPcoNP.NativeBeepCarry
import Shared.Beeping.NPcoNP.NativeCarryReturn83
import Shared.Beeping.NPcoNP.NativeReturnSelectorProgress
import Shared.Beeping.NPcoNP.NativeHalfState93Progress

/-! Physical event preservation through the marked transition, carry,
state-28 cleanup, and selector return. These do not identify a graph PC. -/
namespace Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeCarryReturn83
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeReturnSelectorProgress
open Shared.Beeping.NPcoNP.NativeSelectorEntryProgress
open Shared.Beeping.NPcoNP.NativeHalfState93Progress
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Given two blank tails and a right-hand marker, the flagged transition
and its complete carry/cleanup reach state 83 with exactly one event. The
complete output tape and protected prefix are retained. -/
theorem beep_to83 (h p z b : Int) (t : Int → Bool)
    (ht : t h=true) (hzpos : z<h) (hbpos : h<b)
    (left : ∀ q≤z, t q=false) (right : ∀ q, b≤q → t q=false)
    (hp : h<p) (hone : t p=true) :
    ∃ (j l n : Nat) (stop : Int) (out : Int → Bool), 0<n ∧
      let mark := h-1-(j : Int)
      let scanHead := mark+1
      let u := put (result (put t h false) (h-1) j) (scanHead+(l : Int)) false
      let head28 := scanHead+(l : Int)+1
      head28≤p+1 ∧ head28-1≤stop ∧ out mark=true ∧
      u (stop+1)=false ∧ (∀ q, head28≤q → q≤stop → u q=true) ∧
      out=put (clearRange u head28 (stop+1)) stop true ∧
      (∀ q, q<mark → out q=t q) ∧
      physical.advance (cfg 99 h t) (1+((j+1)+(l+1)+n))=cfg 83 (mark-1) out ∧
      physical.wordFrom (cfg 99 h t) (1+((j+1)+(l+1)+n))=[true] := by
  let u := put t h false
  have hleft : ∀ q≤z, u q=false := by
    intro q hq
    change put t h false q=false
    rw [put_other t h q false (by omega)]
    exact left q hq
  have hright : ∀ q, b≤q → u q=false := by
    intro q hq
    change put t h false q=false
    rw [put_other t h q false (by omega)]
    exact right q hq
  have hone' : u p=true := by
    change put t h false p=true
    rw [put_other t h p false (by omega)]
    exact hone
  obtain ⟨j,l,n,stop,out,hn,hbound,hstop,hmark,hzero,hones,heq,hprefix,hseg⟩ :=
    carry_to83 (h-1) p z b u hleft hright (by omega) hone'
  have hframe : ∀ q, q<h-1-(j : Int) → out q=t q := by
    intro q hq
    rw [hprefix q hq]
    change put t h false q=t q
    exact put_other t h q false (by omega)
  obtain ⟨ha,hw⟩ := beep_then_silent h t ht ((j+1)+(l+1)+n) _ hseg
  exact ⟨j,l,n,stop,out,hn,hbound,hstop,hmark,hzero,hones,heq,hframe,ha,hw⟩

/-- At every reachable beep, a right-hand marker yields a finite return to
state 83, preserves the prefix before its new marker, and emits one event.
The two blank tails follow from finite-time blank-start support. -/
theorem reachable_beep_to83 (time : Nat) (hb : machine.system.BeepAt time)
    (p : Int) (hp : (machine.system.run time).head<p)
    (hone : (machine.system.run time).tape p=true) :
    ∃ (n : Nat) (mark : Int) (out : Int → Bool), 1<n ∧
      mark<(machine.system.run time).head ∧ out mark=true ∧
      (∀ q, q<mark → out q=(machine.system.run time).tape q) ∧
      physical.advance (machine.system.run time) n=cfg 83 (mark-1) out ∧
      physical.wordFrom (machine.system.run time) n=[true] := by
  let c := machine.system.run time
  have hs : c.state.val=99 ∧ c.tape c.head=true := (beepAt_iff time).mp hb
  have hc : c=cfg 99 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    have hstate : c.state=(99 : Fin 284) := Fin.ext hs.1
    simpa only [hstate] using he
  obtain ⟨leftBound,hleft⟩ := run_has_left_zero time
  obtain ⟨rightBound,hright⟩ := run_has_right_zero time
  let z := min leftBound (c.head-1)
  let b := max rightBound (c.head+1)
  have hz : ∀ q≤z, c.tape q=false := by
    intro q hq
    exact hleft q (le_trans hq (min_le_left _ _))
  have hr : ∀ q, b≤q → c.tape q=false := by
    intro q hq
    exact hright q (le_trans (le_max_left _ _) hq)
  obtain ⟨j,l,n,_stop,out,hn,_hbound,_hstop,hmark,_hzero,_hones,_heq,hprefix,ha,hw⟩ :=
    beep_to83 c.head p z b c.tape hs.2 (by dsimp [z]; omega)
      (by dsimp [b]; omega) hz hr hp hone
  refine ⟨1+((j+1)+(l+1)+n),c.head-1-(j : Int),out,by omega,by
    change c.head-1-(j : Int)<c.head
    omega,
    hmark,hprefix,?_,?_⟩
  · simpa only [←hc] using ha
  · simpa only [←hc] using hw

/-- The ordered-bit physical system and scalar machine have identical
configuration advances, even though their event outputs have different types. -/
theorem physical_advance (c : Config 284) (n : Nat) :
    physical.advance c n=machine.system.advance c n := by
  change (machineWordSystem machine (BitLabels.fromFlags machine)).advance c n=_
  rw [← ScalarWordRefinement.beepBits_machine]
  simp [ScalarWordRefinement.beepBits,ScalarWordRefinement.advance_ofBeep]

/-- A paid silent physical segment contributes no Boolean output symbols. -/
theorem silent_physical (c e : Config 284) (n : Nat)
    (hs : silentSegment machine c e n) :
    physical.advance c n=e ∧ physical.wordFrom c n=[] := by
  change (machineWordSystem machine (BitLabels.fromFlags machine)).advance c n=e ∧
    (machineWordSystem machine (BitLabels.fromFlags machine)).wordFrom c n=[]
  rw [← ScalarWordRefinement.beepBits_machine]
  constructor
  · simpa [ScalarWordRefinement.beepBits,W] using hs.1
  · unfold ScalarWordRefinement.beepBits
    rw [WordEventSystem.map_wordFrom]
    change ((W machine).wordFrom c n).map (fun _ => true)=[]
    rw [hs.2]
    rfl

/-- Append a silent segment to any one-event segment, preserving its exact
word and accounting for both finite durations. -/
theorem append_silent (start mid finish : Config 284) (n m : Nat)
    (ha : physical.advance start n=mid) (hw : physical.wordFrom start n=[true])
    (hs : silentSegment machine mid finish m) :
    physical.advance start (n+m)=finish ∧ physical.wordFrom start (n+m)=[true] := by
  obtain ⟨hnext,hquiet⟩ := silent_physical mid finish m hs
  constructor
  · rw [WordEventSystem.advance_add,ha,hnext]
  · rw [WordEventSystem.wordFrom_add,ha,hw,hquiet]
    rfl

/-- A reachable beep with a right-hand marker reaches the next state-93
selector boundary with exactly one event. The state-83 prefix and marker
survive because the intervening selector preserves the entire tape. -/
theorem reachable_beep_to93 (time : Nat) (hb : machine.system.BeepAt time)
    (p : Int) (hp : (machine.system.run time).head<p)
    (hone : (machine.system.run time).tape p=true) :
    ∃ (n : Nat) (mark : Int) (e : Config 284), 1<n ∧ e.state=93 ∧
      mark<(machine.system.run time).head ∧ e.tape mark=true ∧
      (∀ q, q<mark → e.tape q=(machine.system.run time).tape q) ∧
      physical.advance (machine.system.run time) n=e ∧
      physical.wordFrom (machine.system.run time) n=[true] := by
  obtain ⟨n,mark,out,hn,hmarkpos,hmark,hprefix,ha,hw⟩ :=
    reachable_beep_to83 time hb p hp hone
  have hrun : machine.system.run (time+n)=cfg 83 (mark-1) out := by
    rw [EventSystem.run_add,←physical_advance]
    exact ha
  have h83 : (machine.system.run (time+n)).state=83 := by rw [hrun]; rfl
  obtain ⟨m,e,hm,he,htape,hs⟩ := reachable_83_to_93 (time+n) h83
  have ht : e.tape=out := by simpa only [hrun,cfg] using htape
  have hs' : silentSegment machine (cfg 83 (mark-1) out) e m := by simpa only [hrun] using hs
  obtain ⟨had,hword⟩ := append_silent _ _ _ n m ha hw hs'
  refine ⟨n+m,mark,e,by omega,he,hmarkpos,?_,?_,had,hword⟩
  · rw [ht]; exact hmark
  · intro q hq; rw [ht]; exact hprefix q hq

/-- The following actual dispatch also finishes silently. Its precise
source-graph instruction remains an independent invariant obligation. -/
theorem reachable_beep_to_exit (time : Nat) (hb : machine.system.BeepAt time)
    (p : Int) (hp : (machine.system.run time).head<p)
    (hone : (machine.system.run time).tape p=true) :
    ∃ (n : Nat) (e : Config 284), 1<n ∧ Exit e.state ∧
      physical.advance (machine.system.run time) n=e ∧
      physical.wordFrom (machine.system.run time) n=[true] := by
  obtain ⟨n,_mark,c,hn,h93,_hpos,_hbit,_hprefix,ha,hw⟩ :=
    reachable_beep_to93 time hb p hp hone
  have hrun : machine.system.run (time+n)=c := by
    rw [EventSystem.run_add,←physical_advance]
    exact ha
  have hstate : (machine.system.run (time+n)).state=93 := by rw [hrun]; exact h93
  obtain ⟨m,e,hm,he,hs⟩ := reachable_93_to_exit (time+n) hstate
  have hs' : silentSegment machine c e m := by simpa only [hrun] using hs
  obtain ⟨had,hword⟩ := append_silent _ _ _ n m ha hw hs'
  exact ⟨n+m,e,by omega,he,had,hword⟩

/-- In particular, every beep on a non-eventually-silent run reaches the
next literal dispatch with exactly one event. -/
theorem nonsilent_beep_to_exit (h : ¬ machine.system.EventuallySilent)
    (time : Nat) (hb : machine.system.BeepAt time) :
    ∃ (n : Nat) (e : Config 284), 1<n ∧ Exit e.state ∧
      physical.advance (machine.system.run time) n=e ∧
      physical.wordFrom (machine.system.run time) n=[true] := by
  obtain ⟨p,hp,hone⟩ := nonsilent_beep_has_right_marker h time hb
  exact reachable_beep_to_exit time hb p hp hone

#print axioms beep_to83
#print axioms reachable_beep_to83
#print axioms silent_physical
#print axioms append_silent
#print axioms reachable_beep_to93
#print axioms reachable_beep_to_exit
#print axioms nonsilent_beep_to_exit
end Shared.Beeping.NPcoNP.NativeBeepReturn
