import Shared.Beeping.NPcoNP.NativePostAbsenceUnitScan
import Shared.Beeping.NPcoNP.NativeAllZeroNextUnit
import Shared.Beeping.NPcoNP.NativeAllZeroNextReturn
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14

/-! The unit increment following a post-absence scan. These are supplied
physical-layout statements, not blank-start or graph-refinement assertions. -/
namespace Shared.Beeping.NPcoNP.NativePostAbsenceIncrement
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeAllZeroNextUnit
open Shared.Beeping.NPcoNP.NativeAllZeroNextReturn
open Shared.Beeping.NPcoNP.NativeAllZeroNearCarry
open Shared.Beeping.NPcoNP.NativeAllZeroPositiveDispatch
open Shared.Beeping.NPcoNP.NativePostAbsenceUnitScan
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000
attribute [local irreducible] machine

def selectedTape (a : Int) (r : Nat) (t : Int → Bool) : Int → Bool :=
  clearAt (a+26) (scanOutput a r t)

/-- The selected unit branch sees exactly the filled one-run and its
supplied zero delimiter before the bank. -/
theorem selected_scan_word (a : Int) (r : Nat) (t : Int → Bool)
    (stop : t (a+34+(r : Int))=true) (delimiter : t (a+35+(r : Int))=false) :
    Holds (selectedTape a r t) (a+28) (List.replicate (r+7) true ++ [false]) := by
  let selected := selectedTape a r t
  have hprefix : Holds selected (a+28) (List.replicate (r+6) true) := by
    apply holds_of_get
    intro i hi
    have hb : i<r+6 := by simpa using hi
    have hp : a+28≤a+28+(i : Int) ∧ a+28+(i : Int)<a+34+(r : Int) := by omega
    have hn : a+28+(i : Int)≠a+26 := by omega
    simp [selected,selectedTape,clearAt,hn,scanOutput,fillRange,hp]
  have hmarker : selected (a+34+(r : Int))=true := by
    simp [selected,selectedTape,clearAt,scanOutput,fillRange,setAt,stop]
    omega
  have hzero : selected (a+35+(r : Int))=false := by
    simp [selected,selectedTape,clearAt,scanOutput,fillRange,setAt,delimiter]
  have hpair : Holds selected (a+34+(r : Int)) [true,false] := by
    simp only [Holds]
    exact ⟨hmarker,by simpa only [show a+34+(r : Int)+1=a+35+(r : Int) by omega] using hzero,trivial⟩
  have hfull := holds_append_intro selected (a+28) (List.replicate (r+6) true) [true,false] hprefix (by
    have hp : a+28+((List.replicate (r+6) true).length : Int)=a+34+(r : Int) := by simp; omega
    rw [hp]
    exact hpair)
  have hw : List.replicate (r+6) true ++ [true,false]=List.replicate (r+7) true ++ [false] := by
    have hr : List.replicate (r+7) true=List.replicate (r+6) true ++ [true] := by
      conv_lhs => rw [show r+7=(r+6)+1 by omega,List.replicate_succ']
    rw [hr]
    simp [List.append_assoc]
  simpa only [hw] using hfull

/-- Complete the post-absence round trip, unit increment and unchanged-tape
bank return, with an exact silent duration and a protected left frame. -/
theorem post_absence_increment_return_with_frames (a : Int) (r v : Nat) (rest : List Nat) (t : Int → Bool)
    (hpre : Holds t a (zeroWord.take 24)) (left : t (a-1)=true)
    (mark : t (a+24)=true)
    (corr : ∀ q, a+24<q → q<a+34+(r : Int) → t q=false)
    (stop : t (a+34+(r : Int))=true) (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false])) :
    ∃ e : Config 284, e.state=23 ∧
      silentSegment machine (cfg 93 a t) (cfg 1 (a+25) e.tape)
        (((2*r+70)+28+(r+8)+(v+3+(encode rest).length))+
          ((encode ((v+1)::rest)).length+(r+7)+2)) ∧
      Holds e.tape (a+36+(r : Int)) (encode ((v+1)::rest)) ∧
      e.tape (a+25)=false ∧ e.tape (a+26)=false ∧ e.tape (a+27)=false ∧
      Holds e.tape (a+28) (List.replicate (r+7) true ++ [false]) ∧
      (∀ q, q<a+26 → e.tape q=t q) ∧
      (∀ q, a+36+(r : Int)+(((v+1)+(encode rest).length : Nat):Int)<q → e.tape q=t q) := by
  let output := scanOutput a r t
  let selected := selectedTape a r t
  let base := a+36+(r : Int)
  obtain ⟨hround,hwindow,_hframe⟩ := post_absence_roundtrip a r t hpre left mark corr stop
  have hunit := next_window_to12 (a-2) (r+2) output (by simpa using hwindow)
  have hunit' : silentSegment machine (cfg 93 a output) (cfg 12 (a+28) selected) 28 := by
    have hp : a-2+2=a := by omega
    have hh : a-2+30=a+28 := by omega
    have hd : a-2+28=a+26 := by omega
    simpa only [hp,hh,hd,selected,selectedTape] using hunit
  have hword := selected_scan_word a r t stop delimiter
  have hscan := scan12 (r+7) (a+28) selected hword
  have hscan' : silentSegment machine (cfg 12 (a+28) selected) (cfg 14 base selected) (r+8) := by
    have hp : a+28+((r+7 : Nat):Int)+1=base := by dsimp [base]; push_cast; omega
    have hc : r+7+1=r+8 := by omega
    simpa only [hp,hc] using hscan
  have hbank : Holds selected base (encode (v::rest) ++ [false]) := by
    apply holds_transport t selected _ _ bank
    intro q hq _
    symm
    have hq' : a+36+(r : Int)≤q := by simpa only [base] using hq
    have hf : output q=t q := scan_output_frame a r t q (Or.inr (by omega))
    change (if q=a+26 then false else output q)=t q
    rw [if_neg (by omega)]
    exact hf
  obtain ⟨e,hs,hh,hebank,heframe,hinc⟩ := encoded_increment v rest base selected hbank
  have hzero26 : selected (a+26)=false := by simp [selected,selectedTape,clearAt]
  have hzero27 : selected (a+27)=false := by
    have ht := corr (a+27) (by omega) (by omega)
    simpa [selected,selectedTape,clearAt,output,scanOutput,fillRange,setAt] using ht
  have he26 : e.tape (a+26)=false := (heframe _ (Or.inl (by dsimp [base]; omega))).trans hzero26
  have he27 : e.tape (a+27)=false := (heframe _ (Or.inl (by dsimp [base]; omega))).trans hzero27
  have herun : Holds e.tape (a+28) (List.replicate (r+7) true ++ [false]) := by
    apply holds_transport selected e.tape _ _ hword
    intro q _ hq
    symm
    apply heframe q
    left
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil,Nat.cast_add,Nat.cast_one] at hq
    dsimp [base]
    omega
  have hreturn := bank_run_to1 (v+1) rest (a+26) (r+7) e.tape (by omega)
    he26 (by simpa only [show a+26+1=a+27 by omega] using he27)
    (by simpa only [show a+26+2=a+28 by omega] using herun)
    (by have hp : a+26+2+((r+7 : Nat):Int)+1=base := by dsimp [base]; push_cast; omega
        simpa only [hp] using hebank)
  have hhead : e.head=base+((encode ((v+1)::rest)).length : Int)-2 := by
    rw [hh]
    simp only [encode,List.length_append,block_length,Nat.cast_add,Nat.cast_ofNat]
    push_cast
    omega
  have hecfg : e=cfg 23 e.head e.tape := by
    have hc : e=cfg e.state e.head e.tape := by cases e; rfl
    simpa only [hs] using hc
  have hreturn' : silentSegment machine e (cfg 1 (a+25) e.tape)
      ((encode ((v+1)::rest)).length+(r+7)+2) := by
    have hb : a+26+2+((r+7 : Nat):Int)+1=base := by dsimp [base]; push_cast; omega
    have ht : a+26-1=a+25 := by omega
    dsimp only at hreturn
    rw [hb,←hhead,←hecfg,ht] at hreturn
    exact hreturn
  have h1 := segAdd machine _ _ _ (2*r+70) 28 hround hunit'
  have h2 := segAdd machine _ _ _ _ (r+8) h1 hscan'
  have h3 := segAdd machine _ _ _ _ (v+3+(encode rest).length) h2 hinc
  have hall := segAdd machine _ _ _ _ ((encode ((v+1)::rest)).length+(r+7)+2) h3 hreturn'
  have hleft : ∀ q, q<a+26 → e.tape q=t q := by
    intro q hq
    calc
      e.tape q=selected q := heframe q (Or.inl (by dsimp [base]; omega))
      _=output q := by
        change (if q=a+26 then false else output q)=output q
        rw [if_neg (by omega)]
      _=t q := scan_output_frame a r t q (Or.inl hq)
  have he25 : e.tape (a+25)=false := (hleft _ (by omega)).trans (corr _ (by omega) (by omega))
  have hright : ∀ q, a+36+(r : Int)+(((v+1)+(encode rest).length : Nat):Int)<q → e.tape q=t q := by
    intro q hq
    have hq' : base+(((v+1)+(encode rest).length : Nat):Int)<q := by simpa only [base] using hq
    calc
      e.tape q=selected q := heframe q (Or.inr hq')
      _=output q := by
        change (if q=a+26 then false else output q)=output q
        rw [if_neg (by dsimp [base] at hq'; omega)]
      _=t q := scan_output_frame a r t q (Or.inr (by dsimp [base] at hq'; omega))
  exact ⟨e,hs,hall,hebank,he25,he26,he27,herun,hleft,hright⟩

/-- Retain the earlier increment control interface. -/
theorem post_absence_increment_return_with_control (a : Int) (r v : Nat) (rest : List Nat) (t : Int → Bool)
    (hpre : Holds t a (zeroWord.take 24)) (left : t (a-1)=true)
    (mark : t (a+24)=true)
    (corr : ∀ q, a+24<q → q<a+34+(r : Int) → t q=false)
    (stop : t (a+34+(r : Int))=true) (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false])) :
    ∃ e : Config 284, e.state=23 ∧
      silentSegment machine (cfg 93 a t) (cfg 1 (a+25) e.tape)
        (((2*r+70)+28+(r+8)+(v+3+(encode rest).length))+
          ((encode ((v+1)::rest)).length+(r+7)+2)) ∧
      Holds e.tape (a+36+(r : Int)) (encode ((v+1)::rest)) ∧
      e.tape (a+25)=false ∧ e.tape (a+26)=false ∧ e.tape (a+27)=false ∧
      Holds e.tape (a+28) (List.replicate (r+7) true ++ [false]) ∧
      (∀ q, q<a+26 → e.tape q=t q) := by
  obtain ⟨e,hs,hseg,hbank,h25,h26,h27,hrun,hleft,_hright⟩ :=
    post_absence_increment_return_with_frames a r v rest t hpre left mark corr stop delimiter bank
  exact ⟨e,hs,hseg,hbank,h25,h26,h27,hrun,hleft⟩

/-- Retain the earlier increment-return interface. -/
theorem post_absence_increment_return (a : Int) (r v : Nat) (rest : List Nat) (t : Int → Bool)
    (hpre : Holds t a (zeroWord.take 24)) (left : t (a-1)=true)
    (mark : t (a+24)=true)
    (corr : ∀ q, a+24<q → q<a+34+(r : Int) → t q=false)
    (stop : t (a+34+(r : Int))=true) (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false])) :
    ∃ e : Config 284, e.state=23 ∧
      silentSegment machine (cfg 93 a t) (cfg 1 (a+25) e.tape)
        (((2*r+70)+28+(r+8)+(v+3+(encode rest).length))+
          ((encode ((v+1)::rest)).length+(r+7)+2)) ∧
      Holds e.tape (a+36+(r : Int)) (encode ((v+1)::rest)) ∧
      (∀ q, q<a+26 → e.tape q=t q) := by
  obtain ⟨e,hs,hseg,hbank,_h25,_h26,_h27,_hrun,hframe⟩ :=
    post_absence_increment_return_with_control a r v rest t hpre left mark corr stop delimiter bank
  exact ⟨e,hs,hseg,hbank,hframe⟩

/-- When the two earlier cells are blank, the increment and near carry
return silently to state 93 at the same anchor. -/
theorem post_absence_increment_cycle_with_frame (a : Int) (r v : Nat) (rest : List Nat) (t : Int → Bool)
    (hpre : Holds t a (zeroWord.take 24)) (left : t (a-1)=true)
    (left0 : t (a-2)=false) (absent : t (a-3)=false) (before : t (a-4)=false)
    (mark : t (a+24)=true)
    (corr : ∀ q, a+24<q → q<a+34+(r : Int) → t q=false)
    (stop : t (a+34+(r : Int))=true) (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false])) :
    ∃ e : Config 284, e.state=23 ∧
      let out := put (clearRange (put (put e.tape (a+25) true) (a+28) false)
        (a+29) (a+35+(r : Int))) (a+34+(r : Int)) true
      silentSegment machine (cfg 93 a t) (cfg 93 a out)
        ((((2*r+70)+28+(r+8)+(v+3+(encode rest).length))+
          ((encode ((v+1)::rest)).length+(r+7)+2))+(2*r+53)) ∧
      Holds out (a+36+(r : Int)) (encode ((v+1)::rest)) ∧
      out (a+24)=true ∧ out (a+25)=true ∧
      (∀ q, a+25<q → q<a+34+(r : Int) → out q=false) ∧
      out (a+34+(r : Int))=true ∧ out (a+35+(r : Int))=false ∧
      (∀ q, q<a+24 → out q=t q) ∧
      (∀ q, a+36+(r : Int)+(((v+1)+(encode rest).length : Nat):Int)<q → out q=t q) := by
  obtain ⟨e,hs,hseg,hbank,h25,h26,h27,hrun,hframe,hright⟩ :=
    post_absence_increment_return_with_frames a r v rest t hpre left mark corr stop delimiter bank
  let out := put (clearRange (put (put e.tape (a+25) true) (a+28) false)
    (a+29) (a+35+(r : Int))) (a+34+(r : Int)) true
  have hcarry := near_carry_to83 (a-2) (r+2) e.tape
    (by simpa only [show a-2+27=a+25 by omega] using h25)
    (by simpa only [show a-2+28=a+26 by omega] using h26)
    (by simpa only [show a-2+29=a+27 by omega] using h27)
    (by simpa only [show a-2+30=a+28 by omega,show r+2+5=r+7 by omega] using hrun)
  have hcarry' : silentSegment machine (cfg 1 (a+25) e.tape) (cfg 83 (a+24) out) (2*r+21) := by
    have h1 : a-2+27=a+25 := by omega
    have h2 : a-2+26=a+24 := by omega
    have h3 : a-2+30=a+28 := by omega
    have h4 : a-2+31=a+29 := by omega
    have h5 : a-2+35+((r+2 : Nat):Int)=a+35+(r : Int) := by push_cast; omega
    have h6 : a-2+34+((r+2 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
    have hc : 2*(r+2)+17=2*r+21 := by omega
    simpa only [h1,h2,h3,h4,h5,h6,hc,out] using hcarry
  have houtframe : ∀ q, q<a+24 → out q=t q := by
    intro q hq
    calc
      out q=e.tape q := by
        have hf := near_carry_frame (a-2) (r+2) e.tape q (Or.inl (by omega))
        have h1 : a-2+27=a+25 := by omega
        have h2 : a-2+30=a+28 := by omega
        have h3 : a-2+31=a+29 := by omega
        have h4 : a-2+35+((r+2 : Nat):Int)=a+35+(r : Int) := by push_cast; omega
        have h5 : a-2+34+((r+2 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
        simpa only [h1,h2,h3,h4,h5,out] using hf
      _=t q := hframe q (by omega)
  have hmark : out (a+24)=true := by
    have hf := near_carry_frame (a-2) (r+2) e.tape (a+24) (Or.inl (by omega))
    have he : e.tape (a+24)=true := (hframe _ (by omega)).trans mark
    have h1 : a-2+27=a+25 := by omega
    have h2 : a-2+30=a+28 := by omega
    have h3 : a-2+31=a+29 := by omega
    have h4 : a-2+35+((r+2 : Nat):Int)=a+35+(r : Int) := by push_cast; omega
    have h5 : a-2+34+((r+2 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
    have hout : out (a+24)=e.tape (a+24) := by simpa only [h1,h2,h3,h4,h5,out] using hf
    exact hout.trans he
  have hfirst := oneSeg machine _ _ (NativeHalfSelectorScan.step_one ScanRow.r83 (a+24) out hmark)
  have hfirst' : silentSegment machine (cfg 83 (a+24) out) (cfg 83 (a+23) out) 1 := by
    simpa only [show a+24-1=a+23 by omega] using hfirst
  have hdispatch := (positive_return_dispatch_with_prefix a t out hpre left0 left absent houtframe).2 before
  have hscan := segAdd machine _ _ _ 1 31 hfirst' hdispatch
  have hpre' := segAdd machine _ _ _ _ (2*r+21) hseg hcarry'
  have hall := segAdd machine _ _ _ _ (1+31) hpre' hscan
  have hbank' : Holds out (a+36+(r : Int)) (encode ((v+1)::rest)) := by
    apply holds_transport e.tape out _ _ hbank
    intro q hq _
    symm
    have hf := near_carry_frame (a-2) (r+2) e.tape q (Or.inr (by push_cast; omega))
    have h1 : a-2+27=a+25 := by omega
    have h2 : a-2+30=a+28 := by omega
    have h3 : a-2+31=a+29 := by omega
    have h4 : a-2+35+((r+2 : Nat):Int)=a+35+(r : Int) := by push_cast; omega
    have h5 : a-2+34+((r+2 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
    simpa only [h1,h2,h3,h4,h5,out] using hf
  have hmark25 : out (a+25)=true := by simp [out,put,clearRange]
  have hcorr : ∀ q, a+25<q → q<a+34+(r : Int) → out q=false := by
    intro q hq hq'
    have hcases : q=a+26 ∨ q=a+27 ∨ q=a+28 ∨ a+29≤q := by omega
    rcases hcases with rfl | rfl | rfl | hlarge
    · simp [out,put,clearRange,h26]; omega
    · simp [out,put,clearRange,h27]; omega
    · simp [out,put,clearRange]; omega
    · have hr : a+29≤q ∧ q<a+35+(r : Int) := by omega
      have hn : q≠a+34+(r : Int) := by omega
      simp [out,put,clearRange,hr,hn]
  have hstop : out (a+34+(r : Int))=true := by simp [out,put]
  have hedelim : e.tape (a+35+(r : Int))=false := by
    have hh := (split_ones (r+7) (a+28) e.tape [false] hrun).2
    simp only [Holds,and_true] at hh
    have hp : a+28+((r+7 : Nat):Int)=a+35+(r : Int) := by push_cast; omega
    rw [hp] at hh
    exact hh
  have hdelim : out (a+35+(r : Int))=false := by
    have hf := near_carry_frame (a-2) (r+2) e.tape (a+35+(r : Int)) (Or.inr (by push_cast; omega))
    have h1 : a-2+27=a+25 := by omega
    have h2 : a-2+30=a+28 := by omega
    have h3 : a-2+31=a+29 := by omega
    have h4 : a-2+35+((r+2 : Nat):Int)=a+35+(r : Int) := by push_cast; omega
    have h5 : a-2+34+((r+2 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
    have hout : out (a+35+(r : Int))=e.tape (a+35+(r : Int)) := by
      simpa only [h1,h2,h3,h4,h5,out] using hf
    exact hout.trans hedelim
  have hout_right : ∀ q, a+36+(r : Int)+(((v+1)+(encode rest).length : Nat):Int)<q → out q=t q := by
    intro q hq
    have hf := near_carry_frame (a-2) (r+2) e.tape q (Or.inr (by push_cast at hq ⊢; omega))
    have h1 : a-2+27=a+25 := by omega
    have h2 : a-2+30=a+28 := by omega
    have h3 : a-2+31=a+29 := by omega
    have h4 : a-2+35+((r+2 : Nat):Int)=a+35+(r : Int) := by push_cast; omega
    have h5 : a-2+34+((r+2 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
    have hout : out q=e.tape q := by simpa only [h1,h2,h3,h4,h5,out] using hf
    exact hout.trans (hright q hq)
  have hc : 2*r+21+(1+31)=2*r+53 := by omega
  refine ⟨e,hs,?_,hbank',hmark,hmark25,hcorr,hstop,hdelim,houtframe,hout_right⟩
  simpa only [←Nat.add_assoc,hc] using hall

/-- Retain the earlier increment-cycle control interface. -/
theorem post_absence_increment_cycle (a : Int) (r v : Nat) (rest : List Nat) (t : Int → Bool)
    (hpre : Holds t a (zeroWord.take 24)) (left : t (a-1)=true)
    (left0 : t (a-2)=false) (absent : t (a-3)=false) (before : t (a-4)=false)
    (mark : t (a+24)=true)
    (corr : ∀ q, a+24<q → q<a+34+(r : Int) → t q=false)
    (stop : t (a+34+(r : Int))=true) (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false])) :
    ∃ e : Config 284, e.state=23 ∧
      let out := put (clearRange (put (put e.tape (a+25) true) (a+28) false)
        (a+29) (a+35+(r : Int))) (a+34+(r : Int)) true
      silentSegment machine (cfg 93 a t) (cfg 93 a out)
        ((((2*r+70)+28+(r+8)+(v+3+(encode rest).length))+
          ((encode ((v+1)::rest)).length+(r+7)+2))+(2*r+53)) ∧
      Holds out (a+36+(r : Int)) (encode ((v+1)::rest)) ∧
      out (a+24)=true ∧ out (a+25)=true ∧
      (∀ q, a+25<q → q<a+34+(r : Int) → out q=false) ∧
      out (a+34+(r : Int))=true ∧ out (a+35+(r : Int))=false ∧
      (∀ q, q<a+24 → out q=t q) := by
  obtain ⟨e,hs,hseg,hbank,h24,h25,hcorr,hstop,hdelim,hleft,_hright⟩ :=
    post_absence_increment_cycle_with_frame a r v rest t hpre left left0 absent before mark corr stop delimiter bank
  exact ⟨e,hs,hseg,hbank,h24,h25,hcorr,hstop,hdelim,hleft⟩

#print axioms selected_scan_word
#print axioms post_absence_increment_return
#print axioms post_absence_increment_return_with_control
#print axioms post_absence_increment_return_with_frames
#print axioms post_absence_increment_cycle
#print axioms post_absence_increment_cycle_with_frame
end Shared.Beeping.NPcoNP.NativePostAbsenceIncrement
