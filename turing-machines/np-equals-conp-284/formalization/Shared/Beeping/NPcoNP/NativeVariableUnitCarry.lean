import Shared.Beeping.NPcoNP.NativeUnitSelectorBankIncrement
import Shared.Beeping.NPcoNP.NativeUnitIncrementPadding
import Shared.Beeping.NPcoNP.NativeAllZeroNearCarry

/-! Variable unit selector, increment, bank return and near carry. -/
namespace Shared.Beeping.NPcoNP.NativeVariableUnitCarry
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeAllZeroNextReturn
open Shared.Beeping.NPcoNP.NativeAllZeroNearCarry
open Shared.Beeping.NPcoNP.NativeUnitSelectorBankIncrement
open Shared.Beeping.NPcoNP.NativeUnitIncrementPadding
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- Given the indicated unit selector, zero pair, finite one-run and bank,
the literal machine increments the first bank value, returns through state 1,
and completes the near carry. The whole output tape and exact time are stated. -/
theorem variable_unit_increment_carry_with_control (t : Int → Bool) (a : Int) (k z s v : Nat)
    (ws rest : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ 1::0::z::ws)))
    (zero0 : t (a+((2*k : Nat):Int)+3)=false)
    (zero1 : t (a+((2*k : Nat):Int)+5)=false)
    (run : Holds t (a+((2*k : Nat):Int)+6) (List.replicate (s+5) true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+4+((s+8 : Nat):Int))
      (encode (v::rest) ++ [false])) :
    let d := a+((2*k : Nat):Int)+4
    let x := d+((s+8 : Nat):Int)
    ∃ e : Config 284, e.state=23 ∧
      let out := put (clearRange (put (put e.tape (d-1) true) (d+2) false)
        (d+3) (d+((s+7 : Nat):Int))) (d+((s+6 : Nat):Int)) true
      Holds out x (encode ((v+1)::rest)) ∧
      out (d-1)=true ∧ (∀ q, d-1<q → q<d+((s+6 : Nat):Int) → out q=false) ∧
      out (d+((s+6 : Nat):Int))=true ∧ out (d+((s+7 : Nat):Int))=false ∧
      (∀ q, q<d-1 → out q=t q) ∧
      (∀ q, x+(((v+1)+(encode rest).length : Nat):Int)<q → out q=t q) ∧
      silentSegment machine (cfg 93 a t) (cfg 83 (d-2) out)
        (((2*k+6)+(s+6)+(v+3+(encode rest).length))+
          ((encode ((v+1)::rest)).length+(s+5)+2)+(2*s+17)) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let x := d+((s+8 : Nat):Int)
  have hrun : Holds t (d+2) (List.replicate (s+5) true ++ [false]) := by
    have hp : d+2=a+((2*k : Nat):Int)+6 := by dsimp [d]; omega
    simpa only [hp] using run
  have hbank : Holds t x (encode (v::rest) ++ [false]) := by simpa only [x,d] using bank
  have hwordarg : Holds t (a+((2*k : Nat):Int)+4+(0:Int)+2)
      (List.replicate (s+5) true ++ [false]) := by
    have hp : a+((2*k : Nat):Int)+4+(0:Int)+2=d+2 := by dsimp [d]; omega
    simpa only [hp] using hrun
  have hx : a+((2*k : Nat):Int)+4+(0:Int)+2+((s+5 : Nat):Int)+1=x := by
    dsimp [x,d]; push_cast; omega
  have hbankarg : Holds t (a+((2*k : Nat):Int)+4+(0:Int)+2+((s+5 : Nat):Int)+1)
      (encode (v::rest) ++ [false]) := by rw [hx]; exact hbank
  obtain ⟨e,hs,hh,hebank,hleft,hframe,hinc⟩ :=
    unit_selector_bank_increment_with_control t a k 0 z (s+5) v ws rest window hwordarg hbankarg
  simp only [Nat.cast_zero,add_zero] at hx hh hebank hleft hframe
  rw [hx] at hh hebank hleft hframe
  have he0 : e.tape (d-1)=false := by
    have hp : d-1=a+((2*k : Nat):Int)+3 := by dsimp [d]; omega
    rw [hleft _ (by dsimp [x]; omega)]
    have ht : t (d-1)=false := by simpa only [hp] using zero0
    change (if d-1=d then false else t (d-1))=false
    rw [if_neg (by omega)]
    exact ht
  have he1 : e.tape d=false := by
    rw [hleft _ (by dsimp [x]; omega)]
    change (if d=d then false else t d)=false
    simp
  have he2 : e.tape (d+1)=false := by
    have hp : d+1=a+((2*k : Nat):Int)+5 := by dsimp [d]; omega
    rw [hleft _ (by dsimp [x]; omega)]
    have ht : t (d+1)=false := by simpa only [hp] using zero1
    change (if d+1=d then false else t (d+1))=false
    rw [if_neg (by omega)]
    exact ht
  have herun : Holds e.tape (d+2) (List.replicate (s+5) true ++ [false]) := by
    apply holds_transport t e.tape _ _ hrun
    intro q hq hq'
    symm
    apply hframe q (by omega)
    left
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil] at hq'
    dsimp [x]
    push_cast at hq'
    omega
  have hback := bank_run_to1 (v+1) rest d (s+5) e.tape (by omega) he1
    (by simpa using he2) (by simpa using herun) (by
      have hp : d+2+((s+5 : Nat):Int)+1=x := by dsimp [x]; push_cast; omega
      simpa only [hp] using hebank)
  have hlen : (encode ((v+1)::rest)).length=(v+1)+(encode rest).length+2 := by
    simp only [encode,List.length_append,block_length]
    omega
  have hhead : e.head=x+((encode ((v+1)::rest)).length : Int)-2 := by
    rw [hh,hlen]
    push_cast
    omega
  have hecfg : e=cfg 23 e.head e.tape := by
    have hc : e=cfg e.state e.head e.tape := by cases e; rfl
    simpa only [hs] using hc
  have hback' : silentSegment machine e (cfg 1 (d-1) e.tape)
      ((encode ((v+1)::rest)).length+(s+5)+2) := by
    have hp : d+2+((s+5 : Nat):Int)+1=x := by dsimp [x]; push_cast; omega
    dsimp only at hback
    rw [hp,←hhead,←hecfg] at hback
    exact hback
  let out := put (clearRange (put (put e.tape (d-1) true) (d+2) false)
    (d+3) (d+((s+7 : Nat):Int))) (d+((s+6 : Nat):Int)) true
  have hcarry := near_carry_to83 (d-28) s e.tape
    (by simpa only [show d-28+27=d-1 by omega] using he0)
    (by simpa only [show d-28+28=d by omega] using he1)
    (by simpa only [show d-28+29=d+1 by omega] using he2)
    (by simpa only [show d-28+30=d+2 by omega] using herun)
  have hcarry' : silentSegment machine (cfg 1 (d-1) e.tape) (cfg 83 (d-2) out) (2*s+17) := by
    have h1 : d-28+27=d-1 := by omega
    have h2 : d-28+26=d-2 := by omega
    have h3 : d-28+30=d+2 := by omega
    have h4 : d-28+31=d+3 := by omega
    have h5 : d-28+35+(s : Int)=d+((s+7 : Nat):Int) := by push_cast; omega
    have h6 : d-28+34+(s : Int)=d+((s+6 : Nat):Int) := by push_cast; omega
    simpa only [h1,h2,h3,h4,h5,h6,out] using hcarry
  have hcarryframe : ∀ q, q<d-1 ∨ d+((s+7 : Nat):Int)≤q → out q=e.tape q := by
    intro q hq
    have hh' := near_carry_frame (d-28) s e.tape q (by
      rcases hq with hq | hq
      · left; omega
      · right; push_cast at hq ⊢; omega)
    have h1 : d-28+27=d-1 := by omega
    have h3 : d-28+30=d+2 := by omega
    have h4 : d-28+31=d+3 := by omega
    have h5 : d-28+35+(s : Int)=d+((s+7 : Nat):Int) := by push_cast; omega
    have h6 : d-28+34+(s : Int)=d+((s+6 : Nat):Int) := by push_cast; omega
    simpa only [h1,h3,h4,h5,h6,out] using hh'
  have hbankout : Holds out x (encode ((v+1)::rest)) := by
    apply holds_transport e.tape out _ _ hebank
    intro q hq _
    exact (hcarryframe q (Or.inr (by dsimp [x] at hq; push_cast at hq ⊢; omega))).symm
  have hmark : out (d-1)=true := by simp [out,put,clearRange] <;> omega
  have hcorr : ∀ q, d-1<q → q<d+((s+6 : Nat):Int) → out q=false := by
    intro q hq hq'
    have hcases : q=d ∨ q=d+1 ∨ q=d+2 ∨ d+3≤q := by omega
    rcases hcases with rfl | rfl | rfl | hlarge
    · simp [out,put,clearRange,he1] <;> omega
    · simp [out,put,clearRange,he2] <;> omega
    · simp [out,put,clearRange] <;> omega
    · have hr : d+3≤q ∧ q<d+((s+7 : Nat):Int) := by omega
      have hn : q≠d+((s+6 : Nat):Int) := by omega
      simp [out,put,clearRange,hr,hn] <;> omega
  have hstop : out (d+((s+6 : Nat):Int))=true := by simp [out,put]
  have hedelim : e.tape (d+((s+7 : Nat):Int))=false := by
    have hh' := (split_ones (s+5) (d+2) e.tape [false] herun).2
    simp only [Holds,and_true] at hh'
    have hp : d+2+((s+5 : Nat):Int)=d+((s+7 : Nat):Int) := by push_cast; omega
    rw [hp] at hh'
    exact hh'
  have hdelim : out (d+((s+7 : Nat):Int))=false :=
    (hcarryframe _ (Or.inr (by omega))).trans hedelim
  have hleftout : ∀ q, q<d-1 → out q=t q := by
    intro q hq
    rw [hcarryframe q (Or.inl hq),hframe q (by omega) (Or.inl (by dsimp [x]; omega))]
  have hrightout : ∀ q, x+(((v+1)+(encode rest).length : Nat):Int)<q → out q=t q := by
    intro q hq
    rw [hcarryframe q (Or.inr (by dsimp [x] at hq; push_cast at hq ⊢; omega)),
      hframe q (by dsimp [x] at hq; push_cast at hq ⊢; omega) (Or.inr hq)]
  have hinc' : silentSegment machine (cfg 93 a t) e ((2*k+6)+(s+6)+(v+3+(encode rest).length)) := by
    simpa only [Nat.cast_zero,add_zero,show s+5+1=s+6 by omega,d,x] using hinc
  have hmid := segAdd machine _ _ _ _ _ hinc' hback'
  have hall := segAdd machine _ _ _ _ (2*s+17) hmid hcarry'
  exact ⟨e,hs,hbankout,hmark,hcorr,hstop,hdelim,hleftout,hrightout,hall⟩

/-- Retain the earlier variable unit-carry interface. -/
theorem variable_unit_increment_carry (t : Int → Bool) (a : Int) (k z s v : Nat)
    (ws rest : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ 1::0::z::ws)))
    (zero0 : t (a+((2*k : Nat):Int)+3)=false)
    (zero1 : t (a+((2*k : Nat):Int)+5)=false)
    (run : Holds t (a+((2*k : Nat):Int)+6) (List.replicate (s+5) true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+4+((s+8 : Nat):Int))
      (encode (v::rest) ++ [false])) :
    let d := a+((2*k : Nat):Int)+4
    let x := d+((s+8 : Nat):Int)
    ∃ e : Config 284, e.state=23 ∧
      let out := put (clearRange (put (put e.tape (d-1) true) (d+2) false)
        (d+3) (d+((s+7 : Nat):Int))) (d+((s+6 : Nat):Int)) true
      Holds out x (encode ((v+1)::rest)) ∧
      (∀ q, q<d-1 → out q=t q) ∧
      (∀ q, x+(((v+1)+(encode rest).length : Nat):Int)<q → out q=t q) ∧
      silentSegment machine (cfg 93 a t) (cfg 83 (d-2) out)
        (((2*k+6)+(s+6)+(v+3+(encode rest).length))+
          ((encode ((v+1)::rest)).length+(s+5)+2)+(2*s+17)) := by
  obtain ⟨e,hs,hbank,_hmark,_hcorr,_hstop,_hdelim,hleft,hright,hseg⟩ :=
    variable_unit_increment_carry_with_control t a k z s v ws rest window zero0 zero1 run bank
  exact ⟨e,hs,hbank,hleft,hright,hseg⟩

#print axioms variable_unit_increment_carry
end Shared.Beeping.NPcoNP.NativeVariableUnitCarry
