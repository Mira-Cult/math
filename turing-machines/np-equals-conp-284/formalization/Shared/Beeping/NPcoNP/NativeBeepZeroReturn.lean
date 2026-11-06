import Shared.Beeping.NPcoNP.NativeBeepReturn
import Shared.Beeping.NPcoNP.NativeHalfMarkerExact
import Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
import Shared.Beeping.NPcoNP.NativeHalfGrammarBranch

/-! A zero carry head fixes the next state-83 head. This exposes a
counterexample to assuming that every selector entry starts with the
prepared grammar prefix. No first-beep reachability is asserted here. -/
namespace Shared.Beeping.NPcoNP.NativeBeepZeroReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState27Scan
open Shared.Beeping.NPcoNP.NativeHalfMarkerRetain
open Shared.Beeping.NPcoNP.NativeHalfMarkerExact
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
open Shared.Beeping.NPcoNP.NativeHalfGrammarBranch
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- A zero at the state-1 head becomes the marker, so the state-83 head is
exactly one cell to its left. The arbitrary original prefix is preserved. -/
theorem zero_carry_to83_detail_with_clear (h p b : Int) (t : Int → Bool)
    (hzero : t h=false) (hp : h<p) (hone : t p=true)
    (right : ∀ q, b≤q → t q=false) :
    ∃ (n : Nat) (out : Int → Bool) (hit stop : Int), 0<n ∧ out h=true ∧
      (∀ q, q<h → out q=t q) ∧
      (∀ q, h<q → (∀ r, h<r → r≤q → t r=false) → out q=false) ∧
      (∀ q, h<q → q<stop → out q=false) ∧
      h<hit ∧ hit≤p ∧ hit≤stop ∧ t hit=true ∧ t stop=true ∧ t (stop+1)=false ∧
      (∀ q, hit<q → q≤stop → t q=true) ∧
      (∀ q, stop≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 83 (h-1) out) n := by
  let first := put t h true
  have hpone : first p=true := by
    change put t h true p=true
    rw [put_other _ _ _ _ (by omega)]
    exact hone
  obtain ⟨l,hzeros,hfirst⟩ := first_one (h+1) p first (by omega) hpone
  let hit := h+1+(l : Int)
  let mid := put first hit false
  let head28 := hit+1
  have hhitp : hit≤p := by
    by_contra hn
    let i := (p-(h+1)).toNat
    have hi : (i : Int)=p-(h+1) := Int.toNat_of_nonneg (by omega)
    have hil : i<l := by dsimp [hit] at hn; omega
    have hz := hzeros i hil
    have he : h+1+(i : Int)=p := by omega
    rw [he,hpone] at hz
    contradiction
  have hmark : mid h=true := by
    change put first hit false h=true
    rw [put_other _ _ _ _ (by dsimp [hit]; omega)]
    simp [first,put]
  have hcorr : ∀ q, h<q → q<head28 → mid q=false := by
    intro q hq hq'
    by_cases he : q=hit
    · subst q; simp [mid,put]
    · let i := (q-(h+1)).toNat
      have hi : (i : Int)=q-(h+1) := Int.toNat_of_nonneg (by omega)
      have hil : i<l := by dsimp [head28,hit] at hq'; omega
      have hz := hzeros i hil
      have heq : h+1+(i : Int)=q := by omega
      rw [heq] at hz
      change put first hit false q=false
      rw [put_other _ _ _ _ he]
      exact hz
  let top := max b head28
  let k := (top-head28).toNat
  have htop : head28≤top := le_max_right _ _
  have hk : (k : Int)=top-head28 := Int.toNat_of_nonneg (by omega)
  have hz : mid (head28+(k : Int))=false := by
    have he : head28+(k : Int)=top := by omega
    rw [he]
    change put first hit false top=false
    rw [put_other _ _ _ _ (by dsimp [head28] at htop; omega)]
    change put t h true top=false
    rw [put_other _ _ _ _ (by dsimp [head28,hit] at htop; omega)]
    exact right top (le_max_left _ _)
  obtain ⟨n,stop,out,hn,hstop,hout,hstopzero,hones,heq,hprefix,hret⟩ :=
    state28_to83_exact head28 h mid (by dsimp [head28,hit]; omega) hmark hcorr k hz
  have hframe : ∀ q, q<h → out q=t q := by
    intro q hq
    rw [hprefix q (by dsimp [head28,hit]; omega)]
    change put first hit false q=t q
    rw [put_other _ _ _ _ (by dsimp [hit]; omega)]
    change put t h true q=t q
    exact put_other _ _ _ _ (by omega)
  have hhit : t hit=true := by
    have hh : first hit=true := hfirst
    change put t h true hit=true at hh
    rw [put_other _ _ _ _ (by dsimp [hit]; omega)] at hh
    exact hh
  have hhitstop : hit≤stop := by dsimp [head28] at hstop; omega
  have hones' : ∀ q, hit<q → q≤stop → t q=true := by
    intro q hq hq'
    have hm := hones q (by dsimp [head28]; omega) hq'
    change put first hit false q=true at hm
    rw [put_other _ _ _ _ (by omega)] at hm
    change put t h true q=true at hm
    rw [put_other _ _ _ _ (by dsimp [hit] at hq; omega)] at hm
    exact hm
  have hstopone : t stop=true := by
    by_cases he : stop=hit
    · simpa only [he] using hhit
    · exact hones' stop (by omega) (le_refl _)
  have hstopzero' : t (stop+1)=false := by
    change put first hit false (stop+1)=false at hstopzero
    rw [put_other _ _ _ _ (by omega)] at hstopzero
    change put t h true (stop+1)=false at hstopzero
    rw [put_other _ _ _ _ (by dsimp [hit] at hhitstop; omega)] at hstopzero
    exact hstopzero
  have hsuffix : ∀ q, stop≤q → out q=t q := by
    intro q hq
    by_cases he : q=stop
    · subst q
      rw [heq]
      simp [put,hstopone]
    · have hgt : stop<q := by omega
      rw [heq]
      change put (Shared.Beeping.NPcoNP.NativeHalfState28Exact.clearRange mid head28 (stop+1)) stop true q=t q
      rw [put_other _ _ _ _ (by omega)]
      have hnot : ¬ (head28≤q ∧ q<stop+1) := by omega
      simp only [Shared.Beeping.NPcoNP.NativeHalfState28Exact.clearRange,if_neg hnot]
      change put first hit false q=t q
      rw [put_other _ _ _ _ (by omega)]
      change put t h true q=t q
      exact put_other _ _ _ _ (by dsimp [hit] at hhitstop; omega)
  have hzeroFrame : ∀ q, h<q → (∀ r, h<r → r≤q → t r=false) → out q=false := by
    intro q hq hall
    have hlt : q<hit := by
      by_contra hn
      have hb := hall hit (by dsimp [hit]; omega) (by omega)
      rw [hhit] at hb
      contradiction
    rw [hprefix q (by dsimp [head28]; omega)]
    change put first hit false q=false
    rw [put_other _ _ _ _ (by omega)]
    change put t h true q=false
    rw [put_other _ _ _ _ (by omega)]
    exact hall q hq (by omega)
  have hcleared : ∀ q, h<q → q<stop → out q=false := by
    intro q hq hqs
    by_cases hbefore : q<hit
    · rw [hprefix q (by dsimp [head28]; omega)]
      exact hcorr q hq (by dsimp [head28]; omega)
    · rw [heq]
      rw [put_other _ _ _ _ (by omega)]
      by_cases hhit : q=hit
      · subst q
        simp [Shared.Beeping.NPcoNP.NativeHalfState28Exact.clearRange,mid,put]
      · simp [Shared.Beeping.NPcoNP.NativeHalfState28Exact.clearRange,
          show head28≤q ∧ q<stop+1 by dsimp [head28]; omega]
  have hs1 := oneSeg machine _ _ (NativeHalfState1Scan.step_zero h t hzero)
  have hs27 := scan_to_one (h+1) first l hzeros hfirst
  have hall := segAdd machine _ _ _ (1+(l+1)) n
    (segAdd machine _ _ _ 1 (l+1) hs1 hs27) hret
  exact ⟨1+(l+1)+n,out,hit,stop,by omega,hout,hframe,hzeroFrame,hcleared,
    by dsimp [hit]; omega,hhitp,hhitstop,hhit,hstopone,hstopzero',hones',hsuffix,hall⟩

/-- The established detail interface follows from the stronger cleared-interval result. -/
theorem zero_carry_to83_detail (h p b : Int) (t : Int → Bool)
    (hzero : t h=false) (hp : h<p) (hone : t p=true)
    (right : ∀ q, b≤q → t q=false) :
    ∃ (n : Nat) (out : Int → Bool) (hit stop : Int), 0<n ∧ out h=true ∧
      (∀ q, q<h → out q=t q) ∧
      (∀ q, h<q → (∀ r, h<r → r≤q → t r=false) → out q=false) ∧
      h<hit ∧ hit≤p ∧ hit≤stop ∧ t hit=true ∧ t stop=true ∧ t (stop+1)=false ∧
      (∀ q, hit<q → q≤stop → t q=true) ∧
      (∀ q, stop≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 83 (h-1) out) n := by
  obtain ⟨n,out,hit,stop,hn,hm,hprefix,hzeroFrame,_hclear,hhit,hp',hs,
      hhitone,hstop,hstopzero,hones,hsuffix,hsegment⟩ :=
    zero_carry_to83_detail_with_clear h p b t hzero hp hone right
  exact ⟨n,out,hit,stop,hn,hm,hprefix,hzeroFrame,hhit,hp',hs,
    hhitone,hstop,hstopzero,hones,hsuffix,hsegment⟩

/-- A zero carry preserves the protected prefix and its initial zero
corridor, while the original signature remains available to callers. -/
theorem zero_carry_to83_corridor (h p b : Int) (t : Int → Bool)
    (hzero : t h=false) (hp : h<p) (hone : t p=true)
    (right : ∀ q, b≤q → t q=false) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧ out h=true ∧
      (∀ q, q<h → out q=t q) ∧
      (∀ q, h<q → (∀ r, h<r → r≤q → t r=false) → out q=false) ∧
      silentSegment machine (cfg 1 h t) (cfg 83 (h-1) out) n := by
  obtain ⟨n,out,_hit,_stop,hn,hm,hframe,hcorr,_hgt,_hp,_hs,_hh,_ho,_hz,_hones,_hrest,hseg⟩ :=
    zero_carry_to83_detail h p b t hzero hp hone right
  exact ⟨n,out,hn,hm,hframe,hcorr,hseg⟩

/-- The original zero-carry interface, retaining its existing signature. -/
theorem zero_carry_to83 (h p b : Int) (t : Int → Bool)
    (hzero : t h=false) (hp : h<p) (hone : t p=true)
    (right : ∀ q, b≤q → t q=false) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧ out h=true ∧
      (∀ q, q<h → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 83 (h-1) out) n := by
  obtain ⟨n,out,hn,hm,hframe,_hcorr,hs⟩ := zero_carry_to83_corridor h p b t hzero hp hone right
  exact ⟨n,out,hn,hm,hframe,hs⟩

/-- If the two cells immediately left of a flagged head are zero, then a
right marker and a right blank tail force a return to state 83 with a zero
under the head. Consequently the prepared grammar parser rejects there. -/
theorem beep_zero_return_rejects_prepared (h p b : Int) (t : Int → Bool)
    (ht : t h=true) (hz1 : t (h-1)=false) (hz2 : t (h-2)=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hp : h<p) (hone : t p=true) (fuel : Nat) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧ out (h-2)=false ∧
      parsePreparedTape fuel out (h-2)=none ∧
      physical.advance (cfg 99 h t) n=cfg 83 (h-2) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  let u := put t h false
  have hz : u (h-1)=false := by
    change put t h false (h-1)=false
    rw [put_other _ _ _ _ (by omega)]
    exact hz1
  have hone' : u p=true := by
    change put t h false p=true
    rw [put_other _ _ _ _ (by omega)]
    exact hone
  have hr : ∀ q, b≤q → u q=false := by
    intro q hq
    change put t h false q=false
    rw [put_other _ _ _ _ (by omega)]
    exact right q hq
  obtain ⟨n,out,hn,_hmark,hprefix,hseg⟩ :=
    zero_carry_to83 (h-1) p b u hz (by omega) hone' hr
  have hzout : out (h-2)=false := by
    rw [hprefix (h-2) (by omega)]
    change put t h false (h-2)=false
    rw [put_other _ _ _ _ (by omega)]
    exact hz2
  have hparse : parsePreparedTape fuel out (h-2)=none := by
    simp [parsePreparedTape,hzout]
  have hseg' : silentSegment machine (cfg 1 (h-1) u) (cfg 83 (h-2) out) n := by
    simpa only [show h-1-1=h-2 by omega] using hseg
  obtain ⟨ha,hw⟩ := beep_then_silent h t ht n _ hseg'
  exact ⟨1+n,out,by omega,hzout,hparse,ha,hw⟩

/-- The bounded prepared parser depends only on cells at or left of its
head. This compares executable observations on supplied tape accessors; it
does not assert that the physical machine itself implements the parser. -/
theorem prepared_parser_left_frame (back out : Int → Bool) (p h : Int)
    (hp : h<p) (frame : ∀ q<p, out q=back q) :
    parsePreparedTape 52 out h=parsePreparedTape 52 back h := by
  have hiff : ∀ (name : String) (len : Nat),
      parsePreparedTape 52 out h=some (name,len) ↔
        parsePreparedTape 52 back h=some (name,len) := by
    intro name len
    rw [parsePreparedTape_iff,parsePreparedTape_iff]
    constructor
    · rintro ⟨path,hwalk,hlen,htape⟩
      have hf : ∀ q<p, back q=out q := by intro q hq; exact (frame q hq).symm
      exact ⟨path,hwalk,hlen,downHolds_of_left_frame out back p h path hp hf htape⟩
    · rintro ⟨path,hwalk,hlen,htape⟩
      exact ⟨path,hwalk,hlen,downHolds_of_left_frame back out p h path hp frame htape⟩
  cases hb : parsePreparedTape 52 back h with
  | none =>
    cases ho : parsePreparedTape 52 out h with
    | none => rfl
    | some pair =>
      rcases pair with ⟨name,len⟩
      have hh := (hiff name len).mp ho
      rw [hb] at hh
      contradiction
  | some pair =>
    rcases pair with ⟨name,len⟩
    have hh := (hiff name len).mpr hb
    exact hh

/-- A zero carry head returns to the precise preceding control cell; its
entire prepared-parser result is unchanged from the pre-beep tape. -/
theorem beep_zero_return_preserves_parser (h p b : Int) (t : Int → Bool)
    (ht : t h=true) (hz1 : t (h-1)=false) (hb : h<b)
    (right : ∀ q, b≤q → t q=false) (hp : h<p) (hone : t p=true) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      (∀ q, q<h-1 → out q=t q) ∧
      parsePreparedTape 52 out (h-2)=parsePreparedTape 52 t (h-2) ∧
      physical.advance (cfg 99 h t) n=cfg 83 (h-2) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  let u := put t h false
  have hz : u (h-1)=false := by
    change put t h false (h-1)=false
    rw [put_other _ _ _ _ (by omega)]
    exact hz1
  have hone' : u p=true := by
    change put t h false p=true
    rw [put_other _ _ _ _ (by omega)]
    exact hone
  have hr : ∀ q, b≤q → u q=false := by
    intro q hq
    change put t h false q=false
    rw [put_other _ _ _ _ (by omega)]
    exact right q hq
  obtain ⟨n,out,hn,_hmark,hprefix,hseg⟩ :=
    zero_carry_to83 (h-1) p b u hz (by omega) hone' hr
  have hframe : ∀ q, q<h-1 → out q=t q := by
    intro q hq
    rw [hprefix q hq]
    change put t h false q=t q
    exact put_other _ _ _ _ (by omega)
  have hparse := prepared_parser_left_frame t out (h-1) (h-2) (by omega) hframe
  have hseg' : silentSegment machine (cfg 1 (h-1) u) (cfg 83 (h-2) out) n := by
    simpa only [show h-1-1=h-2 by omega] using hseg
  obtain ⟨ha,hw⟩ := beep_then_silent h t ht n _ hseg'
  exact ⟨1+n,out,by omega,hframe,hparse,ha,hw⟩

/-- On a reachable beep, finite support supplies the right blank tail.
The two left zeros and the right marker remain explicit physical facts. -/
theorem reachable_beep_zero_return (time : Nat) (hb : machine.system.BeepAt time)
    (hz1 : (machine.system.run time).tape ((machine.system.run time).head-1)=false)
    (hz2 : (machine.system.run time).tape ((machine.system.run time).head-2)=false)
    (p : Int) (hp : (machine.system.run time).head<p)
    (hone : (machine.system.run time).tape p=true) (fuel : Nat) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      parsePreparedTape fuel out ((machine.system.run time).head-2)=none ∧
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
  obtain ⟨n,out,hn,_hz,hparse,ha,hw⟩ :=
    beep_zero_return_rejects_prepared c.head p bound c.tape hs.2 hz1 hz2
      (by dsimp [bound]; omega) hr hp hone fuel
  have hadvance : machine.system.advance c n=cfg 83 (c.head-2) out := by
    rw [←physical_advance,hc]
    exact ha
  refine ⟨n,out,hn,hparse,?_,?_⟩
  · rw [EventSystem.run_add]
    exact hadvance
  · simpa only [←hc] using hw

/-- The same parser preservation holds at an actual blank-start beep with a
zero immediately to its left and an existing right-hand marker. -/
theorem reachable_beep_zero_preserves_parser (time : Nat) (hb : machine.system.BeepAt time)
    (hz1 : (machine.system.run time).tape ((machine.system.run time).head-1)=false)
    (p : Int) (hp : (machine.system.run time).head<p)
    (hone : (machine.system.run time).tape p=true) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      (∀ q, q<(machine.system.run time).head-1 → out q=(machine.system.run time).tape q) ∧
      parsePreparedTape 52 out ((machine.system.run time).head-2)=
        parsePreparedTape 52 (machine.system.run time).tape ((machine.system.run time).head-2) ∧
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
  obtain ⟨n,out,hn,hframe,hparse,ha,hw⟩ :=
    beep_zero_return_preserves_parser c.head p bound c.tape hs.2 hz1
      (by dsimp [bound]; omega) hr hp hone
  have hadvance : machine.system.advance c n=cfg 83 (c.head-2) out := by
    rw [←physical_advance,hc]
    exact ha
  refine ⟨n,out,hn,hframe,hparse,?_,?_⟩
  · rw [EventSystem.run_add]
    exact hadvance
  · simpa only [←hc] using hw

/-- Such a beep rules out a proposed invariant saying that every actual
state-83 head begins a successfully parsed prepared grammar path. -/
theorem prepared_everywhere_impossible_of_beep (time : Nat)
    (hb : machine.system.BeepAt time)
    (hz1 : (machine.system.run time).tape ((machine.system.run time).head-1)=false)
    (hz2 : (machine.system.run time).tape ((machine.system.run time).head-2)=false)
    (p : Int) (hp : (machine.system.run time).head<p)
    (hone : (machine.system.run time).tape p=true) (fuel : Nat) :
    ¬ (∀ u : Nat, (machine.system.run u).state=83 →
      parsePreparedTape fuel (machine.system.run u).tape (machine.system.run u).head≠none) := by
  intro hall
  obtain ⟨n,out,_hn,hparse,hrun,_hword⟩ :=
    reachable_beep_zero_return time hb hz1 hz2 p hp hone fuel
  have hs : (machine.system.run (time+n)).state=83 := by rw [hrun]; rfl
  have bad := hall (time+n) hs
  rw [hrun] at bad
  exact bad hparse

#print axioms zero_carry_to83_detail_with_clear
#print axioms zero_carry_to83_detail
#print axioms zero_carry_to83_corridor
#print axioms zero_carry_to83
#print axioms beep_zero_return_rejects_prepared
#print axioms prepared_parser_left_frame
#print axioms beep_zero_return_preserves_parser
#print axioms reachable_beep_zero_return
#print axioms reachable_beep_zero_preserves_parser
#print axioms prepared_everywhere_impossible_of_beep
end Shared.Beeping.NPcoNP.NativeBeepZeroReturn
