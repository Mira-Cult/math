import Shared.Beeping.NPcoNP.Bootstrap284VariableRoundtripBlankRays
import Shared.Beeping.NPcoNP.NativeVariablePositiveRightFrame
import Shared.Beeping.NPcoNP.NativeAllBankDecrementPadding
import Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

/-! The real post-increment redispatch preserves the infinite blank ray. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284VariableRedispatchBlankRays
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
open Shared.Beeping.NPcoNP.Bootstrap284VariableRoundtripBlankRays
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 30000000
theorem zero_pairs_ten : zeroPairs 10=zeroWord.take 20 := by decide
theorem zero_word_20_length : (zeroWord.take 20).length=20 := by decide
theorem zero_word_unit : zeroWord.take 20 ++ [true]=markerWindow (List.replicate 9 0 ++ [1]) := by decide
attribute [local irreducible] markerWindow

theorem blank_start_variable_redispatch_with_blank_rays :
    ∃ (m n k j l : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ 0<l ∧
      Holds out (-3820) (zeroWord.take 20) ∧
      Holds out (-3820) (markerWindow (List.replicate 9 0 ++ [1])) ∧ out (-3821)=true ∧ out (-3822)=false ∧
      out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      (∀ q, q≤ -3823 → out q=false) ∧ out (-3800)=true ∧ out 4=false ∧
      Holds out 5 ((encode (List.replicate 1898 0) ++ [true,false,false]) ++ List.replicate 96 false) ∧
      (∀ q, -3800<q → q<3 → out q=false) ∧ out 3=true ∧
      (∀ q, 5+((encode (List.replicate 1898 0)).length : Int)+1≤q → out q=false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603+32+3825+3829+l+31) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hwindow,h2,hstop,hdelim,hray,hbank,hblank,hseg⟩ :=
    blank_start_variable_positive_roundtrip_with_blank_rays
  let t := fillRange (setAt (-3796)
    (put (clearRange (put (put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true)) (-3794) 3
  have hlen : (encode (List.replicate 10 0 ++ [3,3795])).length=3822 := by
    simp [encode,block_length]
  have hext : Holds t ((-3820:Int)+((encode (List.replicate 10 0 ++ [3,3795])).length : Int)) [true,true,false] := by
    rw [hlen]
    simp only [Holds]
    norm_num
    exact ⟨h2,hstop,hdelim⟩
  have hrep : List.replicate 98 false=[false,false] ++ List.replicate 96 false := by decide
  have hbank' : Holds t ((-3820:Int)+((2*10 : Nat):Int)+4+(3795:Int)+2+4)
      ((encode ((0+1)::List.replicate 1897 0) ++ [false,false]) ++ List.replicate 96 false) := by
    rw [hrep,←List.append_assoc] at hbank
    change Holds t 5 ((encode (1::List.replicate 1897 0) ++ [false,false]) ++ List.replicate 96 false)
    exact hbank
  obtain ⟨l,out,hl,hpairs,hleft0,hleft,hray',hmark,hsep,hresult,hcorr,hstop',hfar,hnext⟩ :=
    variable_positive_bank_redispatch_with_right_frame t (-3820) 10 3795 0 (List.replicate 1897 0)
      (List.replicate 96 false) (by decide) (by simpa using hwindow)
      (by intro q hq; exact hray q (by omega)) hext hbank'
  have hpairs' : Holds out (-3820) (zeroWord.take 20) := by
    have he : zeroPairs 10=zeroWord.take 20 := zero_pairs_ten
    simpa only [he] using hpairs
  have hunit : Holds out (-3820) (markerWindow (List.replicate 9 0 ++ [1])) := by
    have hm : Holds out (-3800) [true] := by simpa [Holds] using hmark
    have hh := holds_append_intro out (-3820) (zeroWord.take 20) [true] hpairs' (by
      have hl : (zeroWord.take 20).length=20 := zero_word_20_length
      simpa [hl] using hm)
    have he : zeroWord.take 20 ++ [true]=markerWindow (List.replicate 9 0 ++ [1]) := zero_word_unit
    simpa only [he] using hh
  have hbankOut : Holds out 5 ((encode (List.replicate 1898 0) ++ [true,false,false]) ++ List.replicate 96 false) := by
    change Holds out 5 ((encode (0::List.replicate 1897 0) ++ [true,false,false]) ++ List.replicate 96 false) at hresult
    exact hresult
  have hblankOut : ∀ q, 5+((encode (List.replicate 1898 0)).length : Int)+1≤q → out q=false := by
    intro q hq
    have hl1 : (encode (List.replicate 1898 0)).length=3796 := by rw [zeros_length]
    have hl2 : (encode (List.replicate 1897 0)).length=3794 := by rw [zeros_length]
    have hl3 : (encode (1::List.replicate 1897 0)).length=3797 := by
      change (block 1 ++ encode (List.replicate 1897 0)).length=3797
      rw [List.length_append,block_length,hl2]
    have hqnum : (3802:Int)≤q := by rw [hl1] at hq; omega
    have hb : 5+2+((List.replicate 0 true ++ (List.replicate 1897 0).flatMap
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
  have hnext' : silentSegment machine (cfg 93 (-3820) t) (cfg 93 (-3820) out) (l+31) := by simpa using hnext
  have hall := segAdd machine _ _ _ _ (l+31) hseg hnext'
  refine ⟨m,n,k,j,l,out,hm,hn,hk,hj,hl,hpairs',hunit,by simpa using hleft,by simpa using hleft0,
    hray' (-3823) (by omega),hray' (-3824) (by omega),hray' (-3825) (by omega),?_,by simpa using hmark,
    by simpa using hsep,hbankOut,?_,by simpa using hstop',hblankOut,?_⟩
  · intro q hq; exact hray' q (by omega)
  · intro q hq hq'; apply hcorr <;> norm_num at * <;> omega
  · simpa [Nat.add_assoc] using hall

#print axioms blank_start_variable_redispatch_with_blank_rays
end Shared.Beeping.NPcoNP.Bootstrap284VariableRedispatchBlankRays
