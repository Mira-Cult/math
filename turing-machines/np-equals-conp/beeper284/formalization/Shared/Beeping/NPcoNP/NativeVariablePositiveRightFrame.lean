import Shared.Beeping.NPcoNP.NativeVariablePositiveRedispatch
import Shared.Beeping.NPcoNP.NativePositiveSelectorDirect
import Shared.Beeping.NPcoNP.NativePositiveBankPadding
import Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
import Shared.Beeping.NPcoNP.NativeShortPositiveWindow
import Shared.Beeping.NPcoNP.NativeVariableShortDispatch

/-! Variable positive bank decrement and shortened selector redispatch. -/
namespace Shared.Beeping.NPcoNP.NativeVariablePositiveRightFrame
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeManyTerminalWindow
open Shared.Beeping.NPcoNP.NativePositiveSelectorDirect
open Shared.Beeping.NPcoNP.NativePositiveBankPadding
open Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
open Shared.Beeping.NPcoNP.NativeShortPositiveWindow
open Shared.Beeping.NPcoNP.NativeVariableShortDispatch
open Shared.Beeping.NPcoNP.NativeVariablePositiveRedispatch
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

theorem variable_positive_bank_redispatch_with_right_frame (t : Int → Bool) (a : Int) (k r v : Nat)
    (rest : List Nat) (pad : List Bool) (hk : k≤13)
    (window : Holds t (a-2) (markerWindow (List.replicate (k+1) 0 ++ [3,r])))
    (blank : ∀ q, q<a-2 → t q=false)
    (extension : Holds t (a+((encode (List.replicate k 0 ++ [3,r])).length : Int))
      [true,true,false])
    (bank : Holds t (a+((2*k : Nat):Int)+4+(r : Int)+2+4)
      ((encode ((v+1)::rest) ++ [false,false]) ++ pad)) :
    let d := a+((2*k : Nat):Int)+4
    let x := d+(r : Int)+2+4
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      Holds out a (zeroPairs k) ∧ out (a-2)=false ∧ out (a-1)=true ∧
      (∀ q, q<a-2 → out q=false) ∧ out (d-4)=true ∧ out (x-1)=false ∧
      Holds out x ((encode (v::rest) ++ [true,false,false]) ++ pad) ∧
      (∀ q, d-4<q → q<x-2 → out q=false) ∧ out (x-2)=true ∧
      (∀ q, x+2+((List.replicate v true ++ rest.flatMap
        (fun z => false :: List.replicate (z+1) true)).length : Int)<q → out q=t q) ∧
      silentSegment machine (cfg 93 a t) (cfg 93 a out) (n+31) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let x := d+(r : Int)+2+4
  have hprefix : Holds t (a-2) (zeroPairs (k+1)) := by
    rw [positive_selector_pairs] at window
    exact holds_prefix_word t (a-2) (zeroPairs (k+1))
      ([false] ++ block 3 ++ List.replicate (r+1) true) window
  have heq : markerWindow (List.replicate (k+1) 0 ++ [3,r]) =
      [false,true] ++ markerWindow (List.replicate k 0 ++ [3,r]) := by
    have he : List.replicate (k+1) 0 ++ [3,r]=0::(List.replicate k 0 ++ [3,r]) := by simp [List.replicate_succ]
    rw [he,marker_zero_cons]
  have hwfull := window
  rw [positive_selector_pairs] at hwfull
  -- The selector itself is recovered from the supplied prefix and word.
  have hw : Holds t a (markerWindow (List.replicate k 0 ++ [0+3,r])) := by
    have hw0 : Holds t (a-2) (markerWindow (List.replicate (k+1) 0 ++ [3,r])) := by
      rw [positive_selector_pairs]
      exact hwfull
    rw [heq] at hw0
    have hh := holds_append_tail t (a-2) [false,true] (markerWindow (List.replicate k 0 ++ [3,r])) hw0
    have hp : a-2+(([false,true].length : Nat):Int)=a := by norm_num
    simpa only [hp,Nat.zero_add] using hh
  have hcarry := selector_carry_general t a k r (by simpa using hw)
  have hbank : Holds t x (encode ((v+1)::rest) ++ [false,false]) := by
    apply holds_prefix_word t x (encode ((v+1)::rest) ++ [false,false]) pad
    simpa only [x,d] using bank
  obtain ⟨n,out,hn,hmark,hdelim,hresult,hcorr,hstop,hleft,hright,hseg⟩ :=
    terminal_positive_direct_control t a k r 2 v rest hw (by simpa using extension)
      (by simpa only [d,x,Nat.cast_ofNat,Nat.cast_zero,add_zero] using hbank) hcarry
  have hleft' : ∀ q, q<d-4 → out q=t q := by simpa only [d] using hleft
  have hprefix' : Holds out (a-2) (zeroPairs (k+1)) := by
    apply holds_transport t out _ _ hprefix
    intro q _ hq
    rw [zeroPairs_length] at hq
    exact (hleft' q (by dsimp [d]; push_cast at hq; omega)).symm
  have hblank : ∀ q, q<a-2 → out q=false := by
    intro q hq
    exact (hleft' q (by dsimp [d]; omega)).trans (blank q hq)
  have hresult' : Holds out x (encode (v::rest) ++ [true,false,false]) := by simpa only [d,x,Nat.cast_ofNat,Nat.cast_zero,add_zero] using hresult
  have hright' : ∀ q, x+2+((List.replicate v true ++ rest.flatMap
      (fun z => false :: List.replicate (z+1) true)).length : Int)<q → out q=t q := by
    simpa only [d,x,Nat.cast_ofNat,Nat.cast_zero,add_zero] using hright
  have hbankout : Holds out x ((encode (v::rest) ++ [true,false,false]) ++ pad) :=
    positive_bank_padding t out x v rest pad (by simpa only [d,x] using bank) hresult' hright'
  have hpair := hprefix'
  have hsplit : zeroPairs (k+1)=[false,true] ++ zeroPairs k := by rw [zeroPairs]
  rw [hsplit] at hpair
  have htail := holds_append_tail out (a-2) [false,true] (zeroPairs k) hpair
  have hp : a-2+(([false,true].length : Nat):Int)=a := by norm_num
  have hsmall : Holds out a (zeroPairs k) := by simpa only [hp] using htail
  have h0 : out (a-2)=false := by
    simp only [List.cons_append,List.nil_append,Holds] at hpair
    exact hpair.1
  have h1 : out (a-1)=true := by
    simp only [List.cons_append,List.nil_append,Holds] at hpair
    simpa only [show a-2+1=a-1 by omega] using hpair.2.1
  have hdispatch := variable_short_dispatch out (a-2) (k+1) (by omega) (by omega) hprefix' hblank
  have hdispatch' : silentSegment machine (cfg 83 (d-5) out) (cfg 93 a out) 31 := by
    have hh : a-2+((2*(k+1) : Nat):Int)-1=d-5 := by dsimp [d]; push_cast; omega
    have he : a-2+2=a := by omega
    simpa only [hh,he] using hdispatch
  have hseg' : silentSegment machine (cfg 93 a t) (cfg 83 (d-5) out) n := by simpa only [d,x] using hseg
  have hall := segAdd machine _ _ _ n 31 hseg' hdispatch'
  exact ⟨n,out,hn,hsmall,h0,h1,hblank,by simpa only [d] using hmark,
    by simpa only [x,d,Nat.cast_ofNat,Nat.cast_zero,add_zero] using hdelim,hbankout,by simpa only [d,x,Nat.cast_ofNat,Nat.cast_zero,add_zero] using hcorr,
    by simpa only [d,x,Nat.cast_ofNat,Nat.cast_zero,add_zero] using hstop,hright',hall⟩


#print axioms variable_positive_bank_redispatch_with_right_frame
end Shared.Beeping.NPcoNP.NativeVariablePositiveRightFrame
