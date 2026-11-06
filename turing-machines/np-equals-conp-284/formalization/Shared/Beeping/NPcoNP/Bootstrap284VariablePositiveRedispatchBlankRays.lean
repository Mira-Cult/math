import Shared.Beeping.NPcoNP.Bootstrap284VariableNextBlankRays
import Shared.Beeping.NPcoNP.NativeVariablePositiveRightFrame
import Shared.Beeping.NPcoNP.NativeAllBankDecrementPadding
import Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

/-! The real post-increment redispatch preserves the infinite blank ray. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveRedispatchBlankRays
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeVariablePositiveRightFrame
open Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativePostAbsenceUnitScan
open Shared.Beeping.NPcoNP.NativeAllBankDecrementPadding
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284VariableNextBlankRays
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 30000000
theorem zero_pairs_nine : zeroPairs 9=zeroWord.take 18 := by decide
theorem zero_word_18_length : (zeroWord.take 18).length=18 := by decide
theorem zero_word_unit : zeroWord.take 18 ++ [true]=markerWindow (List.replicate 8 0 ++ [1]) := by decide
attribute [local irreducible] markerWindow

theorem blank_start_variable_positive_redispatch_with_blank_rays :
    ∃ (m n k j l p : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ 0<l ∧ 0<p ∧
      Holds out (-3820) (zeroWord.take 18) ∧
      Holds out (-3820) (markerWindow (List.replicate 8 0 ++ [1])) ∧ out (-3821)=true ∧ out (-3822)=false ∧
      out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      (∀ q, q≤ -3823 → out q=false) ∧ out (-3802)=true ∧ out 4=false ∧
      Holds out 5 ((encode (List.replicate 1899 0) ++ [true,false,false]) ++ List.replicate 94 false) ∧
      (∀ q, -3802<q → q<3 → out q=false) ∧ out 3=true ∧
      (∀ q, 5+((encode (List.replicate 1899 0)).length : Int)+1≤q → out q=false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603+32+3825+3829+l+31+7654+22864+7656+p+31) := by
  obtain ⟨m,n,k,j,l,e,hm,hn,hk,hj,hl,hs,hwindow,h2,hstop,hdelim,hray,hbank,hblank,hseg⟩ :=
    blank_start_variable_positive_next_with_blank_rays
  let t := fillRange (setAt (-3798)
    (put (clearRange (put (put e.tape (-3799) true) (-3796) false) (-3795) 4) 3 true)) (-3796) 3
  have hlen : (encode (List.replicate 9 0 ++ [3,3797])).length=3822 := by
    simp [encode,block_length]
  have hext : Holds t ((-3820:Int)+((encode (List.replicate 9 0 ++ [3,3797])).length : Int)) [true,true,false] := by
    rw [hlen]
    simp only [Holds]
    norm_num
    exact ⟨h2,hstop,hdelim⟩
  have hrep : List.replicate 96 false=[false,false] ++ List.replicate 94 false := by decide
  have hbank' : Holds t ((-3820:Int)+((2*9 : Nat):Int)+4+(3797:Int)+2+4)
      ((encode ((0+1)::List.replicate 1898 0) ++ [false,false]) ++ List.replicate 94 false) := by
    rw [hrep,←List.append_assoc] at hbank
    change Holds t 5 ((encode (1::List.replicate 1898 0) ++ [false,false]) ++ List.replicate 94 false)
    exact hbank
  obtain ⟨p,out,hp,hpairs,hleft0,hleft,hray',hmark,hsep,hresult,hcorr,hstop',hfar,hnext⟩ :=
    variable_positive_bank_redispatch_with_right_frame t (-3820) 9 3797 0 (List.replicate 1898 0)
      (List.replicate 94 false) (by decide) (by simpa using hwindow)
      (by intro q hq; exact hray q (by omega)) hext hbank'
  have hpairs' : Holds out (-3820) (zeroWord.take 18) := by
    have he : zeroPairs 9=zeroWord.take 18 := zero_pairs_nine
    simpa only [he] using hpairs
  have hunit : Holds out (-3820) (markerWindow (List.replicate 8 0 ++ [1])) := by
    have hm : Holds out (-3802) [true] := by simpa [Holds] using hmark
    have hh := holds_append_intro out (-3820) (zeroWord.take 18) [true] hpairs' (by
      have hl : (zeroWord.take 18).length=18 := zero_word_18_length
      simpa [hl] using hm)
    have he : zeroWord.take 18 ++ [true]=markerWindow (List.replicate 8 0 ++ [1]) := zero_word_unit
    simpa only [he] using hh
  have hbankOut : Holds out 5 ((encode (List.replicate 1899 0) ++ [true,false,false]) ++ List.replicate 94 false) := by
    change Holds out 5 ((encode (0::List.replicate 1898 0) ++ [true,false,false]) ++ List.replicate 94 false) at hresult
    exact hresult
  have hblankOut : ∀ q, 5+((encode (List.replicate 1899 0)).length : Int)+1≤q → out q=false := by
    intro q hq
    have hl1 : (encode (List.replicate 1899 0)).length=3798 := by rw [zeros_length]
    have hl2 : (encode (List.replicate 1898 0)).length=3796 := by rw [zeros_length]
    have hl3 : (encode (1::List.replicate 1898 0)).length=3799 := by
      change (block 1 ++ encode (List.replicate 1898 0)).length=3799
      rw [List.length_append,block_length,hl2]
    have hqnum : (3804:Int)≤q := by rw [hl1] at hq; omega
    have hb : 5+2+((List.replicate 0 true ++ (List.replicate 1898 0).flatMap
        (fun z => false :: List.replicate (z+1) true)).length : Int)<q := by
      rw [List.replicate_zero,List.nil_append,flat_length,hl2]
      omega
    have hf : out q=t q := by
      apply hfar
      norm_num only [Nat.reduceMul,Nat.cast_ofNat,Int.reduceAdd,Int.reduceNeg,add_zero]
      exact hb
    rw [hf]
    apply hblank
    rw [hl3]
    omega
  have hnext' : silentSegment machine (cfg 93 (-3820) t) (cfg 93 (-3820) out) (p+31) := by simpa using hnext
  have hall := segAdd machine _ _ _ _ (p+31) hseg hnext'
  refine ⟨m,n,k,j,l,p,out,hm,hn,hk,hj,hl,hp,hpairs',hunit,by simpa using hleft,by simpa using hleft0,
    hray' (-3823) (by omega),hray' (-3824) (by omega),hray' (-3825) (by omega),?_,by simpa using hmark,
    by simpa using hsep,hbankOut,?_,by simpa using hstop',hblankOut,?_⟩
  · intro q hq; exact hray' q (by omega)
  · intro q hq hq'; apply hcorr <;> norm_num at * <;> omega
  · simpa [Nat.add_assoc] using hall

#print axioms blank_start_variable_positive_redispatch_with_blank_rays
end Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveRedispatchBlankRays
