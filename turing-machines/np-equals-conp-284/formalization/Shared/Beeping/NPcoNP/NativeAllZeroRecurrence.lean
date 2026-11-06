import Shared.Beeping.NPcoNP.NativeAllZeroActualDelimiter
import Shared.Beeping.NPcoNP.NativeAllZeroCycleDispatch
import Shared.Beeping.NPcoNP.NativeAllZeroAbsentExact

/-! A finite-depth invariant for repeated marker-present all-zero cycles.
The depth counts supplied left markers and blank bank padding; this module
does not assert that the invariant is reached from blank start. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroRecurrence
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeAllZeroPositiveCycle
open Shared.Beeping.NPcoNP.NativeAllZeroCyclePadding
open Shared.Beeping.NPcoNP.NativeAllZeroActualDelimiter
open Shared.Beeping.NPcoNP.NativeAllZeroCycleDispatch
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentDispatch
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentReturn
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentExact
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000
attribute [local irreducible] machine

/-- One stage has enough alternating markers and bank padding for `depth`
further cycles. The bank starts at the invariant position `a+36+r`. -/
structure Stage (a : Int) (r v : Nat) (rest : List Nat) (depth : Nat) (t : Int → Bool) : Prop where
  window : Holds t a (markerWindow (List.replicate 13 0 ++ [0]))
  left : ∀ i : Nat, i<depth+1 → t (a-2*(i : Int)-1)=true ∧ t (a-2*(i : Int)-2)=false
  marker : t (a+28)=true
  nextZero : t (a+29)=false
  firstZero : t (a+30)=false
  secondZero : t (a+31)=false
  zeros : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false
  stop : t (a+34+(r : Int))=true
  delimiter : t (a+35+(r : Int))=false
  bank : Holds t (a+36+(r : Int))
    (encode (v::rest) ++ List.replicate (2*depth+3) false)

/-- One whole silent selector cycle consumes two supplied padding cells,
appends a zero bank value and moves the anchor left by two cells. -/
theorem stage_step_with_right_frame (a : Int) (r v depth : Nat) (rest : List Nat) (t : Int → Bool)
    (s : Stage a r v rest (depth+1) t) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      silentSegment machine (cfg 93 a t) (cfg 93 (a-2) out) n ∧
      Stage (a-2) (r+2) v (rest ++ [0]) depth out ∧
      (∀ q, q<a+26 → out q=t q) ∧
      (∀ q, a+36+(r : Int)+((encode (v::rest)).length : Int)<q → out q=t q) := by
  have hleft0 : t (a-2)=false := by simpa using (s.left 0 (by omega)).2
  have hearlier : t (a-1)=true := by simpa using (s.left 0 (by omega)).1
  have hnext : t (a-3)=true := by
    simpa only [Nat.cast_one,show a-2*(1:Int)-1=a-3 by omega] using (s.left 1 (by omega)).1
  have hzeros : List.replicate (2*(depth+1)+3) false =
      [false,false,false] ++ ([false,false] ++ List.replicate (2*depth) false) := by
    have hp : 2*(depth+1)+3=5+2*depth := by omega
    rw [hp,List.replicate_add]
    rfl
  have hbank : Holds t (a+36+(r : Int))
      ((encode (v::rest) ++ [false,false,false]) ++ ([false,false] ++ List.replicate (2*depth) false)) := by
    simpa [hzeros,List.append_assoc] using s.bank
  obtain ⟨mid,hs,hseg,hwindow,hbefore,hmark,hbit,hdelim,hbankout,hframe⟩ :=
    padded_cycle_with_actual_delimiter a r v rest (List.replicate (2*depth) false) t
      s.window hleft0 hearlier s.marker s.nextZero s.firstZero s.secondZero s.zeros s.stop s.delimiter hbank
  let t1 := setAt (a+29) (setAt (a+30) mid.tape)
  let out := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  have hframe' : ∀ q, q<a+26 → out q=t q := hframe
  have hpref : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false,false,false]) :=
    holds_prefix_word t _ _ ([false,false] ++ List.replicate (2*depth) false) hbank
  obtain ⟨mid2,_hs2,hseg2,_hw2,_hb2,_hm2,_hbank2,_hleft2,hright2⟩ :=
    all_zero_positive_cycle_framed a r v rest t s.window hleft0 hearlier s.marker s.nextZero
      s.firstZero s.secondZero s.zeros s.stop s.delimiter hpref
  let t2 := setAt (a+29) (setAt (a+30) mid2.tape)
  let out2 := outTape (a+30) (r+3) (selectorOutput a r v rest t2)
  have hcfg : cfg 83 (a+25) out=cfg 83 (a+25) out2 := hseg.1.symm.trans hseg2.1
  have heq : out=out2 := congrArg Config.tape hcfg
  have hright : ∀ q, a+36+(r : Int)+((encode (v::rest)).length : Int)<q → out q=t q := by
    intro q hq
    rw [heq]
    apply hright2
    · have hl := bank_suffix_length v rest
      push_cast at *
      omega
    · simp only [encode,List.length_append,block_length,Nat.cast_add,Nat.cast_ofNat] at hq
      push_cast at *
      omega
  have hmarker : out (a-3)=true := hbefore.trans hnext
  have hdispatch := marker_present_dispatch a out hwindow hmarker
  have hseg' := segAdd machine _ _ _ _ 29 hseg hdispatch
  have h27 : out (a+27)=false := by
    have hp : a+30-3=a+27 := by omega
    simpa only [out,hp] using return_clears_after_marker (a+30) (r+3) (selectorOutput a r v rest t1)
  have h28 : out (a+28)=false := by
    apply return_carry_gap
    all_goals omega
  have h29 : out (a+29)=false := by
    apply return_carry_gap
    all_goals omega
  have h30 : out (a+30)=false := by
    dsimp [out]
    rw [return_at_start]
    unfold selectorOutput
    rw [spec_outside _ _ _ _ (Or.inl (by push_cast; omega))]
    simp [clearAt]
  have hrun : ∀ i : Nat, i<(r+2)+2 → out ((a-2)+32+(i : Int))=false := by
    intro i hi
    by_cases hi0 : i=0
    · subst i
      simpa only [Nat.cast_zero,add_zero,show a-2+32=a+30 by omega] using h30
    · by_cases hi1 : i=1
      · subst i
        simpa only [Nat.cast_one,show a-2+32+1=a+31 by omega] using hbit
      · change outTape (a+30) (r+3) (selectorOutput a r v rest t1) ((a-2)+32+(i : Int))=false
        apply return_right_gap
        · omega
        · push_cast at *; omega
  have hstop : out ((a-2)+34+((r+2 : Nat):Int))=true := by
    have hp : (a-2)+34+((r+2 : Nat):Int)=a+30+1+((r+3 : Nat):Int) := by push_cast; omega
    simpa only [out,hp] using return_marker (a+30) (r+3) (selectorOutput a r v rest t1)
  have hdelimiter : out ((a-2)+35+((r+2 : Nat):Int))=false := by
    have hp : (a-2)+35+((r+2 : Nat):Int)=a+35+(r : Int) := by push_cast; omega
    simpa only [hp] using hdelim
  have hbank' : Holds out ((a-2)+36+((r+2 : Nat):Int))
      (encode (v::(rest ++ [0])) ++ List.replicate (2*depth+3) false) := by
    have hp : (a-2)+36+((r+2 : Nat):Int)=a+36+(r : Int) := by push_cast; omega
    have hrep : List.replicate (2*depth+3) false =
        [false,false,false] ++ List.replicate (2*depth) false := by
      have he : 2*depth+3=3+2*depth := by omega
      rw [he,List.replicate_add]
      rfl
    rw [hp,hrep]
    simpa [out,t1,List.append_assoc] using hbankout
  have hstage : Stage (a-2) (r+2) v (rest ++ [0]) depth out := by
    refine ⟨hwindow,?_,?_,?_,?_,?_,hrun,hstop,hdelimiter,hbank'⟩
    · intro i hi
      have h := s.left (i+1) (by omega)
      constructor
      · rw [hframe' _ (by omega)]
        have hp : a-2-2*(i : Int)-1=a-2*((i+1 : Nat):Int)-1 := by push_cast; omega
        simpa only [hp] using h.1
      · rw [hframe' _ (by omega)]
        have hp : a-2-2*(i : Int)-2=a-2*((i+1 : Nat):Int)-2 := by push_cast; omega
        simpa only [hp] using h.2
    · simpa only [show a-2+28=a+26 by omega] using hmark
    · simpa only [show a-2+29=a+27 by omega] using h27
    · simpa only [show a-2+30=a+28 by omega] using h28
    · simpa only [show a-2+31=a+29 by omega] using h29
  refine ⟨_,out,?_,hseg',hstage,hframe',hright⟩
  omega

/-- Retain the earlier one-step interface. -/
theorem stage_step (a : Int) (r v depth : Nat) (rest : List Nat) (t : Int → Bool)
    (s : Stage a r v rest (depth+1) t) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      silentSegment machine (cfg 93 a t) (cfg 93 (a-2) out) n ∧
      Stage (a-2) (r+2) v (rest ++ [0]) depth out ∧
      (∀ q, q<a+26 → out q=t q) := by
  obtain ⟨n,out,hn,hseg,hstage,hleft,_hright⟩ := stage_step_with_right_frame a r v depth rest t s
  exact ⟨n,out,hn,hseg,hstage,hleft⟩

/-- Any supplied finite depth is exhausted by that many positive-length,
silent cycles. The anchor shifts left by two per cycle and the bank gains
the corresponding number of zero-valued entries. -/
theorem stage_iterate_with_frame (depth : Nat) (a : Int) (r v : Nat) (rest : List Nat) (t : Int → Bool)
    (s : Stage a r v rest depth t) :
    ∃ (n : Nat) (out : Int → Bool), depth≤n ∧
      silentSegment machine (cfg 93 a t)
        (cfg 93 (a-2*(depth : Int)) out) n ∧
      Stage (a-2*(depth : Int)) (r+2*depth) v (rest ++ List.replicate depth 0) 0 out ∧
      (∀ q, q<a-2*(depth : Int)+26 → out q=t q) := by
  induction depth generalizing a r rest t with
  | zero =>
    refine ⟨0,t,by omega,?_,?_,?_⟩
    · simp [silentSegment,WordEventSystem.advance,WordEventSystem.wordFrom]
    · simpa using s
    · intro q _; rfl
  | succ depth ih =>
    obtain ⟨m,next,hm,hstep,hnext,hframe⟩ := stage_step a r v depth rest t s
    obtain ⟨k,out,hk,hrest,hfinal,hframe'⟩ := ih (a-2) (r+2) (rest ++ [0]) next hnext
    have hhead : (a-2)-2*(depth : Int)=a-2*((depth+1 : Nat):Int) := by push_cast; omega
    have hparam : (r+2)+2*depth=r+2*(depth+1) := by omega
    have hvals : (rest ++ [0]) ++ List.replicate depth 0 =
        rest ++ List.replicate (depth+1) 0 := by simp [List.replicate_succ,List.append_assoc]
    rw [hhead] at hrest hfinal
    rw [hparam,hvals] at hfinal
    have hall := segAdd machine _ _ _ m k hstep hrest
    refine ⟨m+k,out,by omega,hall,hfinal,?_⟩
    intro q hq
    calc
      out q=next q := hframe' q (by rw [hhead]; exact hq)
      _=t q := hframe q (by push_cast at hq; omega)

/-- Retain the earlier finite-iteration interface. -/
theorem stage_iterate (depth : Nat) (a : Int) (r v : Nat) (rest : List Nat) (t : Int → Bool)
    (s : Stage a r v rest depth t) :
    ∃ (n : Nat) (out : Int → Bool), depth≤n ∧
      silentSegment machine (cfg 93 a t)
        (cfg 93 (a-2*(depth : Int)) out) n ∧
      Stage (a-2*(depth : Int)) (r+2*depth) v (rest ++ List.replicate depth 0) 0 out := by
  obtain ⟨n,out,hn,hseg,hstage,_hframe⟩ := stage_iterate_with_frame depth a r v rest t s
  exact ⟨n,out,hn,hseg,hstage⟩

/-- The complete blank ray after the bank survives any supplied finite
number of cycles, while the protected left frame is retained. -/
theorem stage_iterate_with_blank_ray (depth : Nat) (a : Int) (r v : Nat)
    (rest : List Nat) (t : Int → Bool) (s : Stage a r v rest depth t)
    (blank : ∀ q, a+36+(r : Int)+((encode (v::rest)).length : Int)≤q → t q=false) :
    ∃ (n : Nat) (out : Int → Bool), depth≤n ∧
      silentSegment machine (cfg 93 a t) (cfg 93 (a-2*(depth : Int)) out) n ∧
      Stage (a-2*(depth : Int)) (r+2*depth) v (rest ++ List.replicate depth 0) 0 out ∧
      (∀ q, q<a-2*(depth : Int)+26 → out q=t q) ∧
      (∀ q, (a-2*(depth : Int))+36+((r+2*depth : Nat):Int)+
        ((encode (v::(rest ++ List.replicate depth 0))).length : Int)≤q → out q=false) := by
  induction depth generalizing a r rest t with
  | zero =>
    refine ⟨0,t,by omega,?_,?_,?_,?_⟩
    · simp [silentSegment,WordEventSystem.advance,WordEventSystem.wordFrom]
    · simpa using s
    · intro q _; rfl
    · simpa using blank
  | succ depth ih =>
    obtain ⟨m,next,hm,hstep,hnext,hleft,hright⟩ := stage_step_with_right_frame a r v depth rest t s
    have hnewblank : ∀ q, (a-2)+36+((r+2 : Nat):Int)+
        ((encode (v::(rest ++ [0]))).length : Int)≤q → next q=false := by
      intro q hq
      have he : encode (v::(rest ++ [0]))=encode (v::rest) ++ [true,false] := by
        have hv : v::(rest ++ [0])=(v::rest) ++ [0] := by simp
        rw [hv,append_zero_block]
      have hl : (encode (v::(rest ++ [0]))).length=(encode (v::rest)).length+2 := by
        rw [he]; simp
      rw [hright q (by rw [hl] at hq; push_cast at hq; omega)]
      apply blank q
      rw [hl] at hq
      push_cast at hq
      omega
    obtain ⟨k,out,hk,hrest,hfinal,hframe,hfinalblank⟩ :=
      ih (a-2) (r+2) (rest ++ [0]) next hnext hnewblank
    have hhead : (a-2)-2*(depth : Int)=a-2*((depth+1 : Nat):Int) := by push_cast; omega
    have hparam : (r+2)+2*depth=r+2*(depth+1) := by omega
    have hvals : (rest ++ [0]) ++ List.replicate depth 0 =
        rest ++ List.replicate (depth+1) 0 := by simp [List.replicate_succ,List.append_assoc]
    rw [hhead] at hrest hfinal hfinalblank
    rw [hparam,hvals] at hfinal hfinalblank
    have hall := segAdd machine _ _ _ m k hstep hrest
    refine ⟨m+k,out,by omega,hall,hfinal,?_,hfinalblank⟩
    intro q hq
    calc
      out q=next q := hframe q (by rw [hhead]; exact hq)
      _=t q := hleft q (by push_cast at hq; omega)

#print axioms stage_step
#print axioms stage_step_with_right_frame
#print axioms stage_iterate
#print axioms stage_iterate_with_frame
#print axioms stage_iterate_with_blank_ray
end Shared.Beeping.NPcoNP.NativeAllZeroRecurrence
