import Shared.Beeping.NPcoNP.NativeBeepZeroReturn
import Shared.Beeping.NPcoNP.Grammar284ForwardParser

/-! Ascending control-word observation after an event. The finite path
matches a graph operation label, but it does not by itself identify the
executing graph program counter or establish a compiler simulation. -/
namespace Shared.Beeping.NPcoNP.NativeBeepForwardControl
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepZeroReturn
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- The observed local layout produces the ascending prepared path
`110100` after the paid physical beep and return to state 83. Every tape and
marker hypothesis is explicit; the parser is a mathematical observation. -/
theorem beep_returns_forward_decrement_bank_with_clear (h p b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true) (hp1 : t (h+1)=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hp : h<p) (hone : t p=true) (hsep : p<separator)
    (hsepzero : t separator=false) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧ out (h-2)=false ∧
      Holds out (h-4) [true,true,false,true,false,false] ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.4.decnz",6) ∧
      (∀ q, q<h-1 → out q=t q) ∧
      (∃ stop, h<stop ∧ stop<separator ∧ t stop=true ∧ t (stop+1)=false ∧ out stop=true ∧
        ∀ q, h≤q → q<stop → out q=false) ∧
      (∀ q, separator≤q → out q=t q) ∧
      physical.advance (cfg 99 h t) n=cfg 83 (h-2) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  let u := put t h false
  have hz : u (h-1)=false := by
    change put t h false (h-1)=false
    rw [put_other _ _ _ _ (by omega)]
    exact hm1
  have hone' : u p=true := by
    change put t h false p=true
    rw [put_other _ _ _ _ (by omega)]
    exact hone
  have hr : ∀ q, b≤q → u q=false := by
    intro q hq
    change put t h false q=false
    rw [put_other _ _ _ _ (by omega)]
    exact right q hq
  obtain ⟨n,out,hit,stop,hn,hmark,hprefix,hcorr,hclear,_hleft,hhitp,hhitstop,
      hhit,hstop,hstopzero,hones,hsuffix,hseg⟩ :=
    zero_carry_to83_detail_with_clear (h-1) p b u hz (by omega) hone' hr
  have huSep : u separator=false := by
    change put t h false separator=false
    rw [put_other _ _ _ _ (by omega)]
    exact hsepzero
  have hstopBefore : stop<separator := by
    by_contra hnot
    have hbad := hones separator (by omega) (by omega)
    rw [huSep] at hbad
    contradiction
  have hbank : ∀ q, separator≤q → out q=t q := by
    intro q hq
    rw [hsuffix q (by omega)]
    change put t h false q=t q
    exact put_other _ _ _ _ (by omega)
  have h4 : out (h-4)=true := by
    rw [hprefix _ (by omega)]
    change put t h false (h-4)=true
    rw [put_other _ _ _ _ (by omega)]
    exact hm4
  have h3 : out (h-3)=true := by
    rw [hprefix _ (by omega)]
    change put t h false (h-3)=true
    rw [put_other _ _ _ _ (by omega)]
    exact hm3
  have h2 : out (h-2)=false := by
    rw [hprefix _ (by omega)]
    change put t h false (h-2)=false
    rw [put_other _ _ _ _ (by omega)]
    exact hm2
  have h0 : out h=false := by
    apply hcorr h (by omega)
    intro r hr0 hr1
    have he : r=h := by omega
    subst r
    simp [u,put]
  have hplus : out (h+1)=false := by
    apply hcorr (h+1) (by omega)
    intro r hr0 hr1
    have he : r=h ∨ r=h+1 := by omega
    rcases he with rfl | rfl
    · simp [u,put]
    · change put t h false (h+1)=false
      rw [put_other _ _ _ _ (by omega)]
      exact hp1
  have hword : Holds out (h-4) [true,true,false,true,false,false] := by
    simp only [Holds]
    refine ⟨h4,?_,?_,?_,?_,?_,trivial⟩
    · have he : h-4+1=h-3 := by omega
      simpa only [he] using h3
    · have he : h-4+1+1=h-2 := by omega
      simpa only [he] using h2
    · have he : h-4+1+1+1=h-1 := by omega
      simpa only [he] using hmark
    · have he : h-4+1+1+1+1=h := by omega
      simpa only [he] using h0
    · have he : h-4+1+1+1+1+1=h+1 := by omega
      simpa only [he] using hplus
  have hparse := observed_path_parse out (h-4) hword
  have hseg' : silentSegment machine (cfg 1 (h-1) u) (cfg 83 (h-2) out) n := by
    simpa only [show h-1-1=h-2 by omega] using hseg
  obtain ⟨ha,hw⟩ := beep_then_silent h t ht n _ hseg'
  have hleft : ∀ q, q<h-1 → out q=t q := by
    intro q hq
    rw [hprefix q hq]
    exact put_other _ _ _ _ (by omega)
  have huzero : u h=false := by simp [u,put]
  have hhitNe : hit≠h := by
    intro he
    rw [he,huzero] at hhit
    contradiction
  have hstophead : h<stop := by omega
  have hstopT : t stop=true := by
    change put t h false stop=true at hstop
    rw [put_other _ _ _ _ (by omega)] at hstop
    exact hstop
  have hstopNext : t (stop+1)=false := by
    change put t h false (stop+1)=false at hstopzero
    rw [put_other _ _ _ _ (by omega)] at hstopzero
    exact hstopzero
  have hstopOut : out stop=true := by
    rw [hsuffix stop (le_refl _)]
    simpa [u,put,show stop≠h by omega] using hstopT
  have hcleared : ∀ q, h≤q → q<stop → out q=false := by
    intro q hq hq'
    exact hclear q (by omega) hq'
  exact ⟨1+n,out,by omega,h2,hword,hparse,hleft,
    ⟨stop,hstophead,hstopBefore,hstopT,hstopNext,hstopOut,hcleared⟩,hbank,ha,hw⟩

/-- The prior prefix and suffix interface follows from the cleared interval. -/
theorem beep_returns_forward_decrement_bank_with_prefix (h p b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true) (hp1 : t (h+1)=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hp : h<p) (hone : t p=true) (hsep : p<separator)
    (hsepzero : t separator=false) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧ out (h-2)=false ∧
      Holds out (h-4) [true,true,false,true,false,false] ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.4.decnz",6) ∧
      (∀ q, q<h-1 → out q=t q) ∧
      (∀ q, separator≤q → out q=t q) ∧
      physical.advance (cfg 99 h t) n=cfg 83 (h-2) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,out,hn,hzero,hword,hparse,hleft,_hclear,hbank,ha,hw⟩ :=
    beep_returns_forward_decrement_bank_with_clear h p b separator t ht hm1 hm2 hm3 hm4 hp1
      hb right hp hone hsep hsepzero
  exact ⟨n,out,hn,hzero,hword,hparse,hleft,hbank,ha,hw⟩

/-- Compatibility interface retaining the established suffix guarantee. -/
theorem beep_returns_forward_decrement_bank (h p b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true) (hp1 : t (h+1)=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hp : h<p) (hone : t p=true) (hsep : p<separator)
    (hsepzero : t separator=false) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧ out (h-2)=false ∧
      Holds out (h-4) [true,true,false,true,false,false] ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.4.decnz",6) ∧
      (∀ q, separator≤q → out q=t q) ∧
      physical.advance (cfg 99 h t) n=cfg 83 (h-2) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,out,hn,hzero,hword,hparse,_hleft,hbank,ha,hw⟩ :=
    beep_returns_forward_decrement_bank_with_prefix h p b separator t ht hm1 hm2 hm3 hm4 hp1
      hb right hp hone hsep hsepzero
  exact ⟨n,out,hn,hzero,hword,hparse,hbank,ha,hw⟩

/-- The earlier forward-path interface follows by choosing a blank cell
past both the supplied right tail and the marker. -/
theorem beep_returns_forward_decrement (h p b : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true) (hp1 : t (h+1)=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hp : h<p) (hone : t p=true) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧ out (h-2)=false ∧
      Holds out (h-4) [true,true,false,true,false,false] ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.4.decnz",6) ∧
      physical.advance (cfg 99 h t) n=cfg 83 (h-2) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  let separator := max b (p+1)
  have hs : t separator=false := right separator (le_max_left _ _)
  obtain ⟨n,out,hn,hzero,hword,hparse,_hbank,ha,hw⟩ :=
    beep_returns_forward_decrement_bank h p b separator t ht hm1 hm2 hm3 hm4 hp1
      hb right hp hone (by dsimp [separator]; omega) hs
  exact ⟨n,out,hn,hzero,hword,hparse,ha,hw⟩

/-- At any reachable beep with the stated finite control window and a
right-hand marker, the same path result holds on the actual return. -/
theorem reachable_beep_returns_forward_decrement (time : Nat)
    (hb : machine.system.BeepAt time)
    (hm1 : (machine.system.run time).tape ((machine.system.run time).head-1)=false)
    (hm2 : (machine.system.run time).tape ((machine.system.run time).head-2)=false)
    (hm3 : (machine.system.run time).tape ((machine.system.run time).head-3)=true)
    (hm4 : (machine.system.run time).tape ((machine.system.run time).head-4)=true)
    (hp1 : (machine.system.run time).tape ((machine.system.run time).head+1)=false)
    (p : Int) (hp : (machine.system.run time).head<p)
    (hone : (machine.system.run time).tape p=true) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      Holds out ((machine.system.run time).head-4) [true,true,false,true,false,false] ∧
      parseForward 52 out ((machine.system.run time).head-4)=
        some ("3.$coalesced.4.decnz",6) ∧
      machine.system.run (time+n)=cfg 83 ((machine.system.run time).head-2) out ∧
      physical.wordFrom (machine.system.run time) n=[true] := by
  let c := machine.system.run time
  have hs : c.state.val=99 ∧ c.tape c.head=true := (beepAt_iff time).mp hb
  have hc : c=cfg 99 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    have hstate : c.state=(99 : Fin 284) := Fin.ext hs.1
    simpa only [hstate] using he
  obtain ⟨b,hb⟩ := run_has_right_zero time
  let bound := max b (c.head+1)
  have hr : ∀ q, bound≤q → c.tape q=false := by
    intro q hq
    exact hb q (le_trans (le_max_left _ _) hq)
  obtain ⟨n,out,hn,_hzero,hword,hparse,ha,hw⟩ :=
    beep_returns_forward_decrement c.head p bound c.tape hs.2 hm1 hm2 hm3 hm4 hp1
      (by dsimp [bound]; omega) hr hp hone
  have hadvance : machine.system.advance c n=cfg 83 (c.head-2) out := by
    rw [←physical_advance,hc]
    exact ha
  refine ⟨n,out,hn,hword,hparse,?_,?_⟩
  · rw [EventSystem.run_add]
    exact hadvance
  · simpa only [←hc] using hw

#print axioms beep_returns_forward_decrement_bank_with_clear
#print axioms beep_returns_forward_decrement_bank_with_prefix
#print axioms beep_returns_forward_decrement_bank
#print axioms beep_returns_forward_decrement
#print axioms reachable_beep_returns_forward_decrement
end Shared.Beeping.NPcoNP.NativeBeepForwardControl
