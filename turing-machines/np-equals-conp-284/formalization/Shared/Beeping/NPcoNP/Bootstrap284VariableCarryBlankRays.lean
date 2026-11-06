import Shared.Beeping.NPcoNP.Bootstrap284ShortReturnBlankRays
import Shared.Beeping.NPcoNP.Bootstrap284ShortZeroReturn
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
import Shared.Beeping.NPcoNP.NativeUnitSelectorBankIncrement
import Shared.Beeping.NPcoNP.NativeVariableUnitCarry
import Shared.Beeping.NPcoNP.NativeVariableWindowWords
import Shared.Beeping.NPcoNP.Grammar284InfiniteWindowBridge

/-! The next shortened unit selector reaches and increments the actual bank. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284VariableCarryBlankRays
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeUnitSelectorBankIncrement
open Shared.Beeping.NPcoNP.NativeVariableUnitCarry
open Shared.Beeping.NPcoNP.NativeShortPositiveWindow
open Shared.Beeping.NPcoNP.NativeVariableWindowWords
open Shared.Beeping.NPcoNP.Grammar284InfiniteWindowBridge
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284ShortZeroReturn
open Shared.Beeping.NPcoNP.Bootstrap284ShortReturnBlankRays
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 16000000

theorem unit_prefix24 : [false,true] ++ markerWindow (List.replicate 10 0 ++ [0])=zeroWord.take 24 := by decide
theorem unit_prefix24_length : (zeroWord.take 24).length=24 := by decide
attribute [local irreducible] markerWindow

/-- The actual shortened selector completes its increment, bank return and
near carry in 22,822 further silent transitions. -/

theorem blank_start_variable_unit_carry_with_blank_rays :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ e.state=23 ∧
      let out := Shared.Beeping.NPcoNP.NativeHalfSweep.put
        (Shared.Beeping.NPcoNP.NativeHalfState28Exact.clearRange
          (Shared.Beeping.NPcoNP.NativeHalfSweep.put (Shared.Beeping.NPcoNP.NativeHalfSweep.put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
      Holds out 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) ∧
      Holds out (-3822) (zeroWord.take 24) ∧
      out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      (∀ q, q≤ -3823 → out q=false) ∧
      out (-3798)=true ∧ out (-3797)=true ∧
      (∀ q, -3797<q → q<3 → out q=false) ∧ out 3=true ∧ out 4=false ∧
      (∀ q, 5+((encode (1::List.replicate 1897 0)).length : Int)≤q → out q=false) ∧
      silentSegment machine (machine.system.run 0) (cfg 83 (-3798) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+22822) := by
  obtain ⟨m,n,k,j,t,hm,hn,hk,hj,hwindow,hl3,hl4,hl5,hray,hlmark,hz7,hz5,h2,h3,h4,hbank,hblank,hseg⟩ :=
    blank_start_short_zero_return_with_blank_rays
  let out := fillRange (setAt (-3796) t) (-3794) 3
  let selected := clearAt (-3796) out
  have hpre : Holds out (-3822) (zeroWord.take 24) := by
    have hwfull := hwindow
    rw [variable_unit_window_word] at hwfull
    have hp := holds_prefix_word out (-3822)
      ([false,true] ++ markerWindow (List.replicate 10 0 ++ [0]))
      ([true,false,true,false] ++ List.replicate 3796 true) (by simpa only [List.append_assoc] using hwfull)
    simpa only [unit_prefix24] using hp
  have hsplit : markerWindow (List.replicate 11 0 ++ [1,0,3795]) =
      [false,true] ++ markerWindow (List.replicate 10 0 ++ [1,0,3795]) := by
    have he : List.replicate 11 0 ++ [1,0,3795]=0::(List.replicate 10 0 ++ [1,0,3795]) := rfl
    rw [he,marker_zero_cons]
  rw [hsplit] at hwindow
  have htail := holds_append_tail out (-3822) [false,true]
    (markerWindow (List.replicate 10 0 ++ [1,0,3795])) hwindow
  have hw : Holds out (-3820) (markerWindow (List.replicate 10 0 ++ 1::0::3795::[])) := by
    simpa only [show (-3822:Int)+(([false,true].length:Nat):Int)= -3820 by norm_num] using htail
  have hrun0 : Holds selected (-3794) (List.replicate 3797 true) := by
    apply holds_of_get
    intro i hi
    have hi' : i<3797 := by simpa only [List.length_replicate] using hi
    have hr : (-3794:Int)≤ -3794+(i : Int) ∧ -3794+(i : Int)<3 := by omega
    have hn : (-3794:Int)+(i : Int)≠ -3796 := by omega
    simp only [List.getElem_replicate]
    simp [selected,clearAt,out,fillRange,hr,hn]
  have hpair : Holds selected 3 [true,false] := by
    simp only [Holds]
    refine ⟨?_,?_,trivial⟩
    · simpa [selected,clearAt] using h3
    · simpa [selected,clearAt] using h4
  have hword : Holds selected (-3794) (List.replicate 3798 true ++ [false]) := by
    have hh := holds_append_intro selected (-3794) (List.replicate 3797 true) [true,false] hrun0 (by simpa only [List.length_replicate,show (-3794:Int)+((3797:Nat):Int)=3 by norm_num] using hpair)
    have he : List.replicate 3797 true ++ [true,false]=List.replicate 3798 true ++ [false] := by
      conv_rhs => rw [show 3798=3797+1 by decide, List.replicate_succ']
      rw [List.append_assoc]
      rfl
    simpa only [he] using hh
  have hword0 : Holds out (-3794) (List.replicate 3798 true ++ [false]) := by
    apply holds_transport selected out _ _ hword
    intro q hq _
    simp [selected,clearAt,show q≠ -3796 by omega]
  have hbankword : encode (0::List.replicate 1897 0) ++ [false] =
      encode (List.replicate 1897 0) ++ [true,false,false] := by
    have he : 0::List.replicate 1897 0=List.replicate 1897 0 ++ [0] := by
      rw [←List.replicate_succ']
      rfl
    rw [he,append_zero_block]
    simp only [List.cons_append,List.nil_append,List.append_assoc]
  have hbank' : Holds out 5 (encode (0::List.replicate 1897 0) ++ [false]) := by
    rw [hbankword]
    exact holds_prefix_word out 5 (encode (List.replicate 1897 0) ++ [true,false,false])
      (List.replicate 98 false) hbank
  obtain ⟨e,hs,hebank,hmark,hcorr,hstop,hdelim,hleft,hright,hnext⟩ :=
    variable_unit_increment_carry_with_control out (-3820) 10 3795 3793 0 [] (List.replicate 1897 0)
      hw (by change out (-3797)=false; exact hz7) (by change out (-3795)=false; exact hz5)
      (by change Holds out (-3794) (List.replicate 3798 true ++ [false]); exact hword0)
      (by change Holds out 5 (encode (0::List.replicate 1897 0) ++ [false]); exact hbank')
  let result := Shared.Beeping.NPcoNP.NativeHalfSweep.put
    (Shared.Beeping.NPcoNP.NativeHalfState28Exact.clearRange
      (Shared.Beeping.NPcoNP.NativeHalfSweep.put (Shared.Beeping.NPcoNP.NativeHalfSweep.put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
  have hlen0 : (encode (List.replicate 1897 0)).length=3794 := by rw [zeros_length]
  have hlen : (encode (1::List.replicate 1897 0)).length=3797 := by
    change (block 1 ++ encode (List.replicate 1897 0)).length=3797
    rw [List.length_append,block_length,hlen0]
  have hnext' : silentSegment machine (cfg 93 (-3820) out) (cfg 83 (-3798) result) 22822 := by
    simp only [hlen,hlen0] at hnext
    norm_num at hnext ⊢
    exact hnext
  have hbankresult : Holds result 5 (encode (1::List.replicate 1897 0)) := by
    change Holds result 5 (encode (1::List.replicate 1897 0)) at hebank
    exact hebank
  have hray' : ∀ q, q≤ -3823 → result q=false := by
    intro q hq
    have hh : result q=out q := by simpa using hleft q (by norm_num; omega)
    exact hh.trans (hray q hq)
  have hblankResult : ∀ q, 5+((encode (1::List.replicate 1897 0)).length : Int)≤q → result q=false := by
    intro q hq
    have hn : (3802 : Int)≤q := by rw [hlen] at hq; omega
    have hh := hright q (by simp only [hlen0]; norm_num; omega)
    have hf : result q=out q := by dsimp only [result]; norm_num at hh ⊢; exact hh
    rw [hf]
    apply hblank
    rw [hlen0]
    omega
  have hprefResult : Holds result (-3822) (zeroWord.take 24) := by
    apply holds_transport out result _ _ hpre
    intro q _ hq
    rw [unit_prefix24_length] at hq
    symm
    have hf := hleft q (by norm_num; omega)
    dsimp only [result]
    norm_num at hf ⊢
    exact hf
  have hpad : Holds result (5+((encode (1::List.replicate 1897 0)).length : Int)) (List.replicate 98 false) :=
    blank_replicate result _ 98 hblankResult
  have hbankfull := holds_append_intro result 5 (encode (1::List.replicate 1897 0)) (List.replicate 98 false) hbankresult hpad
  have hmark0 : result (-3798)=true := by
    have hf := hleft (-3798) (by norm_num)
    dsimp only [result]
    norm_num at hf ⊢
    exact hf.trans hlmark
  have hmark1 : result (-3797)=true := by dsimp only [result]; norm_num at hmark ⊢; exact hmark
  have hgap : ∀ q, -3797<q → q<3 → result q=false := by
    intro q hq hq'
    have hh := hcorr q (by norm_num; omega) (by norm_num; omega)
    dsimp only [result]
    norm_num at hh ⊢
    exact hh
  have hstop' : result 3=true := by dsimp only [result]; norm_num at hstop ⊢; exact hstop
  have hdelim' : result 4=false := by dsimp only [result]; norm_num at hdelim ⊢; exact hdelim
  have hall := segAdd machine _ _ _ _ 22822 hseg hnext'
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbankfull,hprefResult,hray' (-3823) (by omega),
    hray' (-3824) (by omega),hray' (-3825) (by omega),hray',hmark0,hmark1,hgap,hstop',hdelim',hblankResult,hall⟩


#print axioms blank_start_variable_unit_carry_with_blank_rays
end Shared.Beeping.NPcoNP.Bootstrap284VariableCarryBlankRays
