import Shared.Beeping.NPcoNP.NativeVariableUnitRedispatch
import Shared.Beeping.NPcoNP.NativeVariableUnitCarry
import Shared.Beeping.NPcoNP.NativeVariableShortDispatch
import Shared.Beeping.NPcoNP.NativeVariableWindowWords

/-! Variable unit increment/carry followed by a short selector redispatch. -/
namespace Shared.Beeping.NPcoNP.NativeVariableUnitRightFrame
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeUnitIncrementPadding
open Shared.Beeping.NPcoNP.NativeVariableUnitCarry
open Shared.Beeping.NPcoNP.NativeVariableUnitRedispatch
open Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
open Shared.Beeping.NPcoNP.NativeVariableShortDispatch
open Shared.Beeping.NPcoNP.NativeVariableWindowWords
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000
attribute [local irreducible] machine

theorem variable_unit_carry_redispatch_with_right_frame (t : Int → Bool) (a : Int) (k z s v : Nat)
    (ws rest : List Nat) (pad : List Bool) (hk : k≤12)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ 1::0::z::ws)))
    (hprefix : Holds t (a-2) (zeroPairs (k+2)))
    (blank : ∀ q, q<a-2 → t q=false)
    (mark : t (a+((2*k : Nat):Int)+2)=true)
    (zero0 : t (a+((2*k : Nat):Int)+3)=false)
    (zero1 : t (a+((2*k : Nat):Int)+5)=false)
    (run : Holds t (a+((2*k : Nat):Int)+6) (List.replicate (s+5) true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+4+((s+8 : Nat):Int))
      ((encode (v::rest) ++ [false]) ++ pad)) :
    let d := a+((2*k : Nat):Int)+4
    let x := d+((s+8 : Nat):Int)
    ∃ e : Config 284, e.state=23 ∧
      let out := put (clearRange (put (put e.tape (d-1) true) (d+2) false)
        (d+3) (d+((s+7 : Nat):Int))) (d+((s+6 : Nat):Int)) true
      Holds out x (encode ((v+1)::rest) ++ pad) ∧
      Holds out a (markerWindow (List.replicate k 0 ++ [0])) ∧
      out (a-2)=false ∧ out (a-1)=true ∧ (∀ q, q<a-2 → out q=false) ∧
      out (d-2)=true ∧ out (d-1)=true ∧
      (∀ q, d-1<q → q<d+((s+6 : Nat):Int) → out q=false) ∧
      out (d+((s+6 : Nat):Int))=true ∧ out (d+((s+7 : Nat):Int))=false ∧
      (∀ q, x+(((v+1)+(encode rest).length : Nat):Int)<q → out q=t q) ∧
      silentSegment machine (cfg 93 a t) (cfg 93 a out)
        ((((2*k+6)+(s+6)+(v+3+(encode rest).length))+
          ((encode ((v+1)::rest)).length+(s+5)+2)+(2*s+17))+32) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let x := d+((s+8 : Nat):Int)
  have hbank : Holds t x (encode (v::rest) ++ [false]) := by
    apply holds_prefix_word t x (encode (v::rest) ++ [false]) pad
    simpa only [x,d] using bank
  obtain ⟨e,hs,hebank,hmark,hcorr,hstop,hdelim,hleft,hright,hseg⟩ :=
    variable_unit_increment_carry_with_control t a k z s v ws rest window zero0 zero1 run (by simpa [x,d] using hbank)
  let out := put (clearRange (put (put e.tape (d-1) true) (d+2) false)
    (d+3) (d+((s+7 : Nat):Int))) (d+((s+6 : Nat):Int)) true
  have hleft' : ∀ q, q<d-1 → out q=t q := by simpa only [d,out] using hleft
  have hright' : ∀ q, x+(((v+1)+(encode rest).length : Nat):Int)<q → out q=t q := by
    simpa only [d,x,out] using hright
  have hebank' : Holds out x (encode ((v+1)::rest)) := by simpa only [d,x,out] using hebank
  have hbankpad : Holds out x (encode ((v+1)::rest) ++ pad) :=
    unit_increment_padding t out x v rest pad (by simpa only [x,d] using bank) hebank' hright'
  have hpref : Holds out (a-2) (zeroPairs (k+2)) := by
    apply holds_transport t out _ _ hprefix
    intro q _ hq
    rw [zeroPairs_length] at hq
    exact (hleft' q (by dsimp [d]; push_cast at hq; omega)).symm
  have hblank : ∀ q, q<a-2 → out q=false := by
    intro q hq
    exact (hleft' q (by dsimp [d]; omega)).trans (blank q hq)
  have hpair := hpref
  have hsplit : zeroPairs (k+2)=[false,true] ++ zeroPairs (k+1) := by
    have he : k+2=(k+1)+1 := by omega
    rw [he,zeroPairs]
  rw [hsplit] at hpair
  have htail := holds_append_tail out (a-2) [false,true] (zeroPairs (k+1)) hpair
  have hwin : Holds out a (markerWindow (List.replicate k 0 ++ [0])) := by
    rw [zero_window_pairs]
    have hp : a-2+(([false,true].length : Nat):Int)=a := by norm_num
    simpa only [hp] using htail
  have h0 : out (a-2)=false := by
    simp only [List.cons_append,List.nil_append,Holds] at hpair
    exact hpair.1
  have h1 : out (a-1)=true := by
    simp only [List.cons_append,List.nil_append,Holds] at hpair
    simpa only [show a-2+1=a-1 by omega] using hpair.2.1
  have hmark' : out (d-2)=true := by
    have hp : d-2=a+((2*k : Nat):Int)+2 := by dsimp [d]; omega
    rw [hleft' _ (by omega),hp]
    exact mark
  have hfirst : silentSegment machine (cfg 83 (d-2) out) (cfg 83 (d-3) out) 1 := by
    simpa only [show d-2-1=d-3 by omega] using oneSeg machine _ _ (step_one ScanRow.r83 (d-2) out hmark')
  have hdispatch := variable_short_dispatch out (a-2) (k+2) (by omega) (by omega) hpref hblank
  have hdispatch' : silentSegment machine (cfg 83 (d-3) out) (cfg 93 a out) 31 := by
    have hh : a-2+((2*(k+2) : Nat):Int)-1=d-3 := by dsimp [d]; push_cast; omega
    have he : a-2+2=a := by omega
    simpa only [hh,he] using hdispatch
  have h32 := segAdd machine _ _ _ 1 31 hfirst hdispatch'
  have hall := segAdd machine _ _ _ _ 32 hseg h32
  exact ⟨e,hs,hbankpad,hwin,h0,h1,hblank,hmark',by simpa only [d,out] using hmark,
    by simpa only [d,out] using hcorr,by simpa only [d,out] using hstop,
    by simpa only [d,out] using hdelim,hright',hall⟩


#print axioms variable_unit_carry_redispatch_with_right_frame
end Shared.Beeping.NPcoNP.NativeVariableUnitRightFrame
