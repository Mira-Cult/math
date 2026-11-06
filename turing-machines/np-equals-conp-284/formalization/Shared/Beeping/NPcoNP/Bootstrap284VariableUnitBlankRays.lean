import Shared.Beeping.NPcoNP.Bootstrap284VariableZeroBlankRays
import Shared.Beeping.NPcoNP.NativeVariableUnitRightFrame
import Shared.Beeping.NPcoNP.NativeVariableWindowWords
import Shared.Beeping.NPcoNP.NativeShortPositiveWindow
import Shared.Beeping.NPcoNP.Bootstrap284VariableZeroRoundtrip
import Shared.Beeping.NPcoNP.NativeVariableUnitRedispatch

/-! The generalized unit/carry redispatch on the next actual shorter selector. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284VariableUnitBlankRays
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
open Shared.Beeping.NPcoNP.NativeVariableUnitRedispatch
open Shared.Beeping.NPcoNP.NativeVariableUnitRightFrame
open Shared.Beeping.NPcoNP.NativeVariableWindowWords
open Shared.Beeping.NPcoNP.NativeShortPositiveWindow
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284VariableZeroRoundtrip
open Shared.Beeping.NPcoNP.Bootstrap284VariableZeroBlankRays
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 16000000

theorem unit_prefix22 : [false,true] ++ markerWindow (List.replicate 9 0 ++ [0])=zeroPairs 11 := by decide
attribute [local irreducible] markerWindow

theorem blank_start_variable_unit_redispatch_with_blank_rays :
    ∃ (m n k j l : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ 0<l ∧ e.state=23 ∧
      let out := put (clearRange (put (put e.tape (-3799) true) (-3796) false) (-3795) 4) 3 true
      Holds out 5 (encode (1::List.replicate 1898 0) ++ List.replicate 96 false) ∧
      Holds out (-3820) (markerWindow (List.replicate 9 0 ++ [0])) ∧
      out (-3822)=false ∧ out (-3821)=true ∧ (∀ q, q< -3822 → out q=false) ∧
      out (-3800)=true ∧ out (-3799)=true ∧
      (∀ q, -3799<q → q<3 → out q=false) ∧ out 3=true ∧ out 4=false ∧
      (∀ q, 5+((encode (1::List.replicate 1898 0)).length : Int)≤q → out q=false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603+32+3825+3829+l+31+7654+22864) := by
  obtain ⟨m,n,k,j,l,t,hm,hn,hk,hj,hl,hwindow,hbank,hray,hmark,hzero0,hzero1,hstop,hdelim,hblank,hseg⟩ :=
    blank_start_variable_zero_roundtrip_with_blank_rays
  let input := fillRange (setAt (-3798) t) (-3796) 3
  have hprefix : Holds input (-3822) (zeroPairs 11) := by
    have hwfull := hwindow
    rw [variable_unit_window_word] at hwfull
    have hp := holds_prefix_word input (-3822)
      ([false,true] ++ markerWindow (List.replicate 9 0 ++ [0]))
      ([true,false,true,false] ++ List.replicate 3798 true) (by simpa only [List.append_assoc] using hwfull)
    simpa only [unit_prefix22] using hp
  have hsplit : markerWindow (List.replicate 10 0 ++ [1,0,3797]) =
      [false,true] ++ markerWindow (List.replicate 9 0 ++ [1,0,3797]) := by
    have he : List.replicate 10 0 ++ [1,0,3797]=0::(List.replicate 9 0 ++ [1,0,3797]) := rfl
    rw [he,marker_zero_cons]
  rw [hsplit] at hwindow
  have htail := holds_append_tail input (-3822) [false,true]
    (markerWindow (List.replicate 9 0 ++ [1,0,3797])) hwindow
  have hw : Holds input (-3820) (markerWindow (List.replicate 9 0 ++ 1::0::3797::[])) := by
    simpa only [show (-3822:Int)+(([false,true].length:Nat):Int)= -3820 by norm_num] using htail
  have hrun0 : Holds input (-3796) (List.replicate 3799 true) := by
    apply holds_of_get
    intro i hi
    have hi' : i<3799 := by simpa only [List.length_replicate] using hi
    have hr : (-3796:Int)≤ -3796+(i : Int) ∧ -3796+(i : Int)<3 := by omega
    simp only [List.getElem_replicate]
    simp [input,fillRange,hr]
  have hpair : Holds input 3 [true,false] := by
    simp only [Holds]
    exact ⟨hstop,by simpa using hdelim,trivial⟩
  have hrun : Holds input (-3796) (List.replicate 3800 true ++ [false]) := by
    have hh := holds_append_intro input (-3796) (List.replicate 3799 true) [true,false] hrun0 (by simpa only [List.length_replicate,show (-3796:Int)+((3799:Nat):Int)=3 by norm_num] using hpair)
    have he : List.replicate 3799 true ++ [true,false]=List.replicate 3800 true ++ [false] := by
      conv_rhs => rw [show 3800=3799+1 by decide, List.replicate_succ']
      rw [List.append_assoc]
      rfl
    simpa only [he] using hh
  have hbankword : encode (0::List.replicate 1898 0) ++ [false] =
      encode (List.replicate 1898 0) ++ [true,false,false] := by
    have he : 0::List.replicate 1898 0=List.replicate 1898 0 ++ [0] := by
      rw [←List.replicate_succ']
      rfl
    rw [he,append_zero_block]
    simp only [List.cons_append,List.nil_append,List.append_assoc]
  have hbank' : Holds input 5 ((encode (0::List.replicate 1898 0) ++ [false]) ++ List.replicate 96 false) := by
    rw [hbankword]
    exact hbank
  obtain ⟨e,hs,hebank,hewin,he0,he1,heblank,hemark,henext,hecorr,hestop,hedelim,heright,hnext⟩ :=
    variable_unit_carry_redispatch_with_right_frame input (-3820) 9 3797 3795 0 [] (List.replicate 1898 0)
      (List.replicate 96 false) (by decide) hw (by change Holds input (-3822) (zeroPairs 11); exact hprefix)
      (by intro q hq; exact hray q (by omega)) (by simpa using hmark)
      (by change input (-3799)=false; exact hzero0) (by change input (-3797)=false; exact hzero1)
      (by change Holds input (-3796) (List.replicate 3800 true ++ [false]); exact hrun)
      (by change Holds input 5 ((encode (0::List.replicate 1898 0) ++ [false]) ++ List.replicate 96 false); exact hbank')
  let out := put (clearRange (put (put e.tape (-3799) true) (-3796) false) (-3795) 4) 3 true
  have hlen0 : (encode (List.replicate 1898 0)).length=3796 := by rw [zeros_length]
  have hlen : (encode (1::List.replicate 1898 0)).length=3799 := by
    change (block 1 ++ encode (List.replicate 1898 0)).length=3799
    rw [List.length_append,block_length,hlen0]
  have hnext' : silentSegment machine (cfg 93 (-3820) input) (cfg 93 (-3820) out) 22864 := by
    simp only [hlen,hlen0] at hnext
    norm_num at hnext ⊢
    exact hnext
  have hblankOut : ∀ q, 5+((encode (1::List.replicate 1898 0)).length : Int)≤q → out q=false := by
    intro q hq
    have hn : (3804 : Int)≤q := by rw [hlen] at hq; omega
    have hh := heright q (by simp only [hlen0]; norm_num; omega)
    have hf : out q=input q := by dsimp only [out]; norm_num at hh ⊢; exact hh
    rw [hf]
    apply hblank
    rw [hlen0]
    omega
  have hall := segAdd machine _ _ _ _ 22864 hseg hnext'
  exact ⟨m,n,k,j,l,e,hm,hn,hk,hj,hl,hs,by
      change Holds out 5 (encode (1::List.replicate 1898 0) ++ List.replicate 96 false) at hebank
      exact hebank,by simpa using hewin,
    by simpa using he0,by simpa using he1,by simpa using heblank,by simpa using hemark,
    by simpa using henext,by simpa using hecorr,by simpa using hestop,by simpa using hedelim,hblankOut,hall⟩


#print axioms blank_start_variable_unit_redispatch_with_blank_rays
end Shared.Beeping.NPcoNP.Bootstrap284VariableUnitBlankRays
