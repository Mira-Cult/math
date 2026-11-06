import Shared.Beeping.NPcoNP.NativeHalfSelectorExact
import Shared.Beeping.NPcoNP.NativeBeepForwardControl

/-! Exact selector and dispatch for the observed first-event control window.
The left-blank premise is explicit: this does not establish blank-start reachability
or the semantic effect of the selected operation. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
namespace Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepForwardControl
open Shared.Beeping.NPcoNP.Grammar284ForwardParser

/-- State 92 passes a specified finite run of zeroes and then the first one. -/
theorem scan92_exact (k : Nat) (h : Int) (t : Int → Bool)
    (zeros : ∀ i : Nat, i < k → t (h+(i : Int))=false)
    (one : t (h+(k : Int))=true) :
    silentSegment machine (cfg 92 h t) (cfg 93 (h+(k : Int)+1) t) (k+1) := by
  induction k generalizing h with
  | zero =>
    simpa using oneSeg machine _ _ (step92_one h t (by simpa using one))
  | succ k ih =>
    have hz : t h=false := by simpa using zeros 0 (by omega)
    have hz' : ∀ i : Nat, i<k → t ((h+1)+(i : Int))=false := by
      intro i hi
      have v := zeros (i+1) (by omega)
      have he : (h+1)+(i : Int)=h+((i+1 : Nat) : Int) := by push_cast; omega
      simpa only [he] using v
    have ho : t ((h+1)+(k : Int))=true := by
      have he : (h+1)+(k : Int)=h+((Nat.succ k : Nat) : Int) := by push_cast; omega
      simpa only [he] using one
    have hs := segAdd machine _ _ _ 1 (k+1)
      (oneSeg machine _ _ (step92_zero h t hz)) (ih (h+1) hz' ho)
    have he : (h+1)+(k : Int)+1=h+((Nat.succ k : Nat) : Int)+1 := by push_cast; omega
    simpa [he, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

/-- The concrete selector scans 16 cells left and 15 cells right. -/
theorem selector_first_path (h : Int) (t : Int → Bool)
    (h2 : t (h-2)=false) (h3 : t (h-3)=true) (h4 : t (h-4)=true)
    (left : ∀ q, q<h-4 → t q=false) :
    silentSegment machine (cfg 83 (h-2) t) (cfg 93 (h-3) t) 31 := by
  let ks : List Nat := [0,2] ++ List.replicate 12 0
  have hw : downHolds t (h-2) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | exact h2 | (convert h3 using 1 <;> congr 1 <;> omega) |
      (convert h4 using 1 <;> congr 1 <;> omega) | (apply left; omega)
  have hs := (chain_blocks chain83 ks (h-2) t [] (by decide) hw).2
  have hs' : silentSegment machine (cfg 83 (h-2) t) (cfg 92 (h-18) t) 16 := by
    have he : h-2-16=h-18 := by omega
    simpa [ks,blocks,List.replicate_succ,he] using hs
  have hz : ∀ i : Nat, i<14 → t ((h-18)+(i : Int))=false := by
    intro i hi
    apply left
    omega
  have ho : t ((h-18)+(14 : Int))=true := by
    have he : h-18+14=h-4 := by omega
    simpa only [he] using h4
  have hr := scan92_exact 14 (h-18) t hz ho
  have hall := segAdd machine _ _ _ 16 15 hs' hr
  convert hall using 1 <;> congr 1 <;> omega

theorem row93_one : machine.table.row 93 true = ⟨true,.right,94,false⟩ := by decide
theorem row94_zero : machine.table.row 94 false = ⟨false,.right,259,false⟩ := by decide
theorem row259_one : machine.table.row 259 true = ⟨true,.right,166,false⟩ := by decide

/-- Three literal dispatch rows follow the path bits 1, 0, 1, preserving the tape. -/
theorem dispatch_93_to166 (h : Int) (t : Int → Bool)
    (h3 : t (h-3)=true) (h2 : t (h-2)=false) (h1 : t (h-1)=true) :
    silentSegment machine (cfg 93 (h-3) t) (cfg 166 h t) 3 := by
  have w3 : (⟨93,h-3,t⟩ : Config 284).write true=t := by
    rw [← h3]; exact write_current _
  have w2 : (⟨94,h-2,t⟩ : Config 284).write false=t := by
    rw [← h2]; exact write_current _
  have w1 : (⟨259,h-1,t⟩ : Config 284).write true=t := by
    rw [← h1]; exact write_current _
  have s1 : machine.step (cfg 93 (h-3) t)=(cfg 94 (h-2) t,false) := by
    have he : h-3+1=h-2 := by omega
    simpa [cfg,Machine.step,h3,row93_one,Move.apply,w3,he]
  have s2 : machine.step (cfg 94 (h-2) t)=(cfg 259 (h-1) t,false) := by
    have he : h-2+1=h-1 := by omega
    simpa [cfg,Machine.step,h2,row94_zero,Move.apply,w2,he]
  have s3 : machine.step (cfg 259 (h-1) t)=(cfg 166 h t,false) := by
    have he : h-1+1=h := by omega
    simpa [cfg,Machine.step,h1,row259_one,Move.apply,w1,he]
  have s12 := segAdd machine _ _ _ 1 1 (oneSeg machine _ _ s1) (oneSeg machine _ _ s2)
  exact segAdd machine _ _ _ 2 1 s12 (oneSeg machine _ _ s3)

/-- Under an explicit supplied event layout, the flagged transition is followed
by a finite silent selector and dispatch to literal state 166. Both tape frames
and the exact one-event word are retained. This is not an operation-correctness
or blank-start theorem. -/
theorem beep_to_first_dispatch (h p b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true) (hp1 : t (h+1)=false)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hp : h<p) (hone : t p=true) (hsep : p<separator)
    (hsepzero : t separator=false) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      Holds out (h-4) [true,true,false,true,false,false] ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.4.decnz",6) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, separator≤q → out q=t q) ∧
      physical.advance (cfg 99 h t) n=cfg 166 h out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,out,hn,h2,hword,hparse,hprefix,hframe,ha,hw⟩ :=
    beep_returns_forward_decrement_bank_with_prefix h p b separator t ht hm1 hm2 hm3 hm4 hp1
      hb right hp hone hsep hsepzero
  have hl : ∀ q, q<h-4 → out q=false := by
    intro q hq
    rw [hprefix q (by omega)]
    exact left q hq
  have h3 : out (h-3)=true := by
    have hv := hword
    simp only [Holds] at hv
    have he : h-4+1=h-3 := by omega
    simpa only [he] using hv.2.1
  have h4 : out (h-4)=true := by
    have hv := hword
    simp only [Holds] at hv
    exact hv.1
  have h1 : out (h-1)=true := by
    have hv := hword
    simp only [Holds] at hv
    have he : h-4+1+1+1=h-1 := by omega
    simpa only [he] using hv.2.2.2.1
  have hsel := selector_first_path h out h2 h3 h4 hl
  have hdisp := dispatch_93_to166 h out h3 h2 h1
  have hsegment : silentSegment machine (cfg 83 (h-2) out) (cfg 166 h out) 34 :=
    segAdd machine _ _ _ 31 3 hsel hdisp
  obtain ⟨ha',hw'⟩ := append_silent (cfg 99 h t) (cfg 83 (h-2) out) (cfg 166 h out)
    n 34 ha hw hsegment
  exact ⟨n+34,out,by omega,hword,hparse,hl,hframe,ha',hw'⟩

/-- Actual-run form of the conditional result. Reachability of the stated
layout, and operation correctness after state 166, remain separate questions. -/
theorem reachable_beep_to_first_dispatch (time : Nat)
    (hb : machine.system.BeepAt time)
    (hm1 : (machine.system.run time).tape ((machine.system.run time).head-1)=false)
    (hm2 : (machine.system.run time).tape ((machine.system.run time).head-2)=false)
    (hm3 : (machine.system.run time).tape ((machine.system.run time).head-3)=true)
    (hm4 : (machine.system.run time).tape ((machine.system.run time).head-4)=true)
    (hp1 : (machine.system.run time).tape ((machine.system.run time).head+1)=false)
    (left : ∀ q, q<(machine.system.run time).head-4 →
      (machine.system.run time).tape q=false)
    (p separator : Int) (hp : (machine.system.run time).head<p)
    (hone : (machine.system.run time).tape p=true) (hsep : p<separator)
    (hsepzero : (machine.system.run time).tape separator=false) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      Holds out ((machine.system.run time).head-4) [true,true,false,true,false,false] ∧
      parseForward 52 out ((machine.system.run time).head-4)=
        some ("3.$coalesced.4.decnz",6) ∧
      (∀ q, q<(machine.system.run time).head-4 → out q=false) ∧
      (∀ q, separator≤q → out q=(machine.system.run time).tape q) ∧
      machine.system.run (time+n)=cfg 166 (machine.system.run time).head out ∧
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
  obtain ⟨n,out,hn,hword,hparse,hleft,hframe,ha,hw⟩ :=
    beep_to_first_dispatch c.head p bound separator c.tape hs.2 hm1 hm2 hm3 hm4 hp1 left
      (by dsimp [bound]; omega) hr hp hone hsep hsepzero
  have hadvance : machine.system.advance c n=cfg 166 c.head out := by
    rw [←physical_advance,hc]
    exact ha
  refine ⟨n,out,hn,hword,hparse,hleft,hframe,?_,?_⟩
  · rw [EventSystem.run_add]
    exact hadvance
  · simpa only [←hc] using hw

end Shared.Beeping.NPcoNP.NativeFirstDispatch
#print axioms Shared.Beeping.NPcoNP.NativeFirstDispatch.selector_first_path
#print axioms Shared.Beeping.NPcoNP.NativeFirstDispatch.dispatch_93_to166
#print axioms Shared.Beeping.NPcoNP.NativeFirstDispatch.beep_to_first_dispatch
#print axioms Shared.Beeping.NPcoNP.NativeFirstDispatch.reachable_beep_to_first_dispatch
