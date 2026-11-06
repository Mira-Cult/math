import Shared.Beeping.NPcoNP.Bootstrap284ShortPositiveBank
import Shared.Beeping.NPcoNP.NativeVariableShortDispatch

/-! Apply the variable short-selector return to the actual positive bank. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284VariableRedispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
open Shared.Beeping.NPcoNP.NativeVariableShortDispatch
open Shared.Beeping.NPcoNP.Bootstrap284ShortPositiveBank
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- The actual positive-bank return redispatches in exactly 31 silent steps
and exposes the next, shorter unit selector with its left blank ray. -/
theorem blank_start_variable_redispatch :
    ∃ (m n k j l : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ 0<l ∧
      Holds out (-3820) (zeroWord.take 20) ∧
      Holds out (-3820) (markerWindow (List.replicate 9 0 ++ [1])) ∧
      out (-3821)=true ∧ out (-3822)=false ∧ (∀ q, q≤ -3823 → out q=false) ∧
      out (-3800)=true ∧ out 4=false ∧
      Holds out 5 ((encode (List.replicate 1898 0) ++ [true,false,false]) ++ List.replicate 96 false) ∧
      (∀ q, -3800<q → q<3 → out q=false) ∧ out 3=true ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603+32+3825+3829+l+31) := by
  obtain ⟨m,n,k,j,l,e,out,hm,hn,hk,hj,hl,hs,hpre,hmark,hblank,hray,hbank,hcorr,hstop,_hframe,hseg⟩ :=
    blank_start_short_positive_bank_return_with_prefix
  have hdispatch := variable_short_dispatch out (-3822) 11 (by decide) (by decide) hpre
    (by intro q hq; exact hray q (by omega))
  have hdispatch' : silentSegment machine (cfg 83 (-3801) out) (cfg 93 (-3820) out) 31 := by
    simpa using hdispatch
  have hsplit : zeroPairs 11=[false,true] ++ zeroPairs 10 := by rfl
  have hsmall : Holds out (-3820) (zeroWord.take 20) := by
    rw [hsplit] at hpre
    have hh := holds_append_tail out (-3822) [false,true] (zeroPairs 10) hpre
    have he : zeroPairs 10=zeroWord.take 20 := by decide
    have hp : (-3822:Int)+(([false,true].length : Nat):Int)= -3820 := by norm_num
    rw [hp] at hh
    simpa only [he] using hh
  have hleft0 : out (-3822)=false := by
    have hh := hpre
    simp only [hsplit,List.cons_append,List.nil_append,Holds] at hh
    exact hh.1
  have hleft : out (-3821)=true := by
    have hh := hpre
    simp only [hsplit,List.cons_append,List.nil_append,Holds] at hh
    simpa using hh.2.1
  have hunit : Holds out (-3820) (markerWindow (List.replicate 9 0 ++ [1])) := by
    have hm : Holds out (-3800) [true] := by simpa [Holds] using hmark
    have hh := holds_append_intro out (-3820) (zeroWord.take 20) [true] hsmall (by
      have hl : (zeroWord.take 20).length=20 := by decide
      simpa [hl] using hm)
    have he : zeroWord.take 20 ++ [true]=markerWindow (List.replicate 9 0 ++ [1]) := by decide
    simpa only [he] using hh
  have hall := segAdd machine _ _ _ _ 31 hseg hdispatch'
  exact ⟨m,n,k,j,l,out,hm,hn,hk,hj,hl,hsmall,hunit,hleft,hleft0,hray,hmark,hblank,hbank,hcorr,hstop,hall⟩

#print axioms blank_start_variable_redispatch
end Shared.Beeping.NPcoNP.Bootstrap284VariableRedispatch
