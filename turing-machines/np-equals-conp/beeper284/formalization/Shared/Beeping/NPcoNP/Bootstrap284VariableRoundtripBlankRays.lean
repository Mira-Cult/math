import Shared.Beeping.NPcoNP.Bootstrap284VariableCarryBlankRays
import Shared.Beeping.NPcoNP.Bootstrap284ShortNearCarry
import Shared.Beeping.NPcoNP.NativeVariableShortDispatch
import Shared.Beeping.NPcoNP.NativeVariablePositiveRoundtrip

/-! Instantiate the variable positive-selector round trip on the actual run. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284VariableRoundtripBlankRays
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
open Shared.Beeping.NPcoNP.NativeVariableShortDispatch
open Shared.Beeping.NPcoNP.NativeVariablePositiveRoundtrip
open Shared.Beeping.NPcoNP.Bootstrap284ShortNearCarry
open Shared.Beeping.NPcoNP.Bootstrap284VariableCarryBlankRays
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 16000000
attribute [local irreducible] machine

theorem zero_pairs_twelve : zeroPairs 12=zeroWord.take 24 := by decide
theorem zero_word_split : zeroWord.take 24=[false,true] ++ zeroWord.take 22 := by decide
theorem zero_word_prefix : zeroWord.take 22=markerWindow (List.replicate 10 0 ++ [0]) := by decide
attribute [local irreducible] markerWindow

theorem blank_start_variable_positive_roundtrip_with_blank_rays :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ e.state=23 ∧
      let t := put (clearRange (put (put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
      let out := fillRange (setAt (-3796) t) (-3794) 3
      Holds out (-3822) (markerWindow (List.replicate 11 0 ++ [3,3795])) ∧
      out 2=true ∧ out 3=true ∧ out 4=false ∧ (∀ q, q≤ -3823 → out q=false) ∧
      Holds out 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) ∧
      (∀ q, 5+((encode (1::List.replicate 1897 0)).length : Int)≤q → out q=false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603+32+7654) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hbank,hpre,h3,h4,h5,hray,hmark,hmarker,hcorr,hstop,hdelim,hblank,hseg⟩ :=
    blank_start_variable_unit_carry_with_blank_rays
  let t := put (clearRange (put (put e.tape (-3797) true) (-3794) false) (-3793) 4) 3 true
  let out := fillRange (setAt (-3796) t) (-3794) 3
  have hfirst : silentSegment machine (cfg 83 (-3798) t) (cfg 83 (-3799) t) 1 := by
    simpa using oneSeg machine _ _ (step_one ScanRow.r83 (-3798) t hmark)
  have hpairs : Holds t (-3822) (zeroPairs 12) := by
    have he : zeroPairs 12=zeroWord.take 24 := zero_pairs_twelve
    simpa only [he] using hpre
  have hdispatch := variable_short_dispatch t (-3822) 12 (by decide) (by decide) hpairs
    (by intro q hq; exact hray q (by omega))
  have hdispatch' : silentSegment machine (cfg 83 (-3799) t) (cfg 93 (-3820) t) 31 := by simpa using hdispatch
  have hword : zeroWord.take 24=[false,true] ++ zeroWord.take 22 := zero_word_split
  have hpre' := hpre
  rw [hword] at hpre'
  have htail := holds_append_tail t (-3822) [false,true] (zeroWord.take 22) hpre'
  have hprefix : Holds t (-3820) (zeroWord.take 22) := by simpa using htail
  have hleft0 : t (-3822)=false := by
    simp only [List.cons_append,List.nil_append,Holds] at hpre'
    exact hpre'.1
  have hleft1 : t (-3821)=true := by
    simp only [List.cons_append,List.nil_append,Holds] at hpre'
    simpa using hpre'.2.1
  have he : zeroWord.take 22=markerWindow (List.replicate 10 0 ++ [0]) := zero_word_prefix
  have hw : Holds t (-3820) (markerWindow (List.replicate 10 0 ++ [0])) := by simpa only [he] using hprefix
  have hz : ∀ i : Nat, i<3795+2 → t ((-3820:Int)+((2*10 : Nat):Int)+6+(i : Int))=false := by
    intro i hi
    apply hcorr <;> norm_num <;> omega
  obtain ⟨hround,hwindow,hframe⟩ := variable_positive_roundtrip t (-3820) 10 3795 (by decide) hw
    (by intro q hq; exact hray q (by omega)) (by simpa using hleft0) (by simpa using hleft1)
    (by simpa using hmark) (by simpa using hmarker) (by apply hcorr <;> norm_num)
    (by apply hcorr <;> norm_num) hz (by simpa using hstop)
  have hround' : silentSegment machine (cfg 93 (-3820) t) (cfg 93 (-3820) out) 7654 := by
    norm_num at hround ⊢
    exact hround
  have hwin : Holds out (-3822) (markerWindow (List.replicate 11 0 ++ [3,3795])) := by
    change Holds out (-3822) (markerWindow (List.replicate 11 0 ++ [3,3795])) at hwindow
    exact hwindow
  have hf : ∀ q, q< -3796 ∨ 3≤q → out q=t q := by simpa using hframe
  have hray' : ∀ q, q≤ -3823 → out q=false := by
    intro q hq
    exact (hf q (Or.inl (by omega))).trans (hray q hq)
  have hb : Holds out 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) := by
    apply holds_transport t out _ _ hbank
    intro q hq _
    exact (hf q (Or.inr (by omega))).symm
  have ho2 : out 2=true := by simp [out,fillRange]
  have ho3 : out 3=true := (hf 3 (Or.inr (by norm_num))).trans hstop
  have ho4 : out 4=false := (hf 4 (Or.inr (by norm_num))).trans hdelim
  have hright : ∀ q, 5+((encode (1::List.replicate 1897 0)).length : Int)≤q → out q=false := by
    intro q hq
    have hfq : out q=t q := hf q (Or.inr (by omega))
    exact hfq.trans (hblank q hq)
  have h32 := segAdd machine _ _ _ 1 31 hfirst hdispatch'
  have hnext := segAdd machine _ _ _ 32 7654 h32 hround'
  have hall := segAdd machine _ _ _ _ (32+7654) hseg hnext
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hwin,ho2,ho3,ho4,hray',hb,hright,by simpa [Nat.add_assoc] using hall⟩


#print axioms blank_start_variable_positive_roundtrip_with_blank_rays
end Shared.Beeping.NPcoNP.Bootstrap284VariableRoundtripBlankRays
