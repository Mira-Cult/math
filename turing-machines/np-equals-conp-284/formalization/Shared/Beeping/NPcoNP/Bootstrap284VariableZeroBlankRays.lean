import Shared.Beeping.NPcoNP.Bootstrap284VariableRedispatchBlankRays
import Shared.Beeping.NPcoNP.Bootstrap284VariableRedispatch
import Shared.Beeping.NPcoNP.NativeVariableZeroRoundtrip

/-! Instantiate the variable zero-selector round trip on the actual run. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284VariableZeroBlankRays
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeVariableZeroRoundtrip
open Shared.Beeping.NPcoNP.Bootstrap284VariableRedispatch
open Shared.Beeping.NPcoNP.Bootstrap284VariableRedispatchBlankRays
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 16000000

theorem zero_word_prefix : zeroWord.take 20=markerWindow (List.replicate 9 0 ++ [0]) := by decide
attribute [local irreducible] markerWindow

theorem blank_start_variable_zero_roundtrip_with_blank_rays :
    ∃ (m n k j l : Nat) (t : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧ 0<l ∧
      let out := fillRange (setAt (-3798) t) (-3796) 3
      Holds out (-3822) (markerWindow (List.replicate 10 0 ++ [1,0,3797])) ∧
      Holds out 5 ((encode (List.replicate 1898 0) ++ [true,false,false]) ++ List.replicate 96 false) ∧
      (∀ q, q≤ -3823 → out q=false) ∧
      out (-3800)=true ∧ out (-3799)=false ∧ out (-3797)=false ∧ out 3=true ∧ out 4=false ∧
      (∀ q, 5+((encode (List.replicate 1898 0)).length : Int)+1≤q → out q=false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622+7597+7603+32+3825+3829+l+31+7654) := by
  obtain ⟨m,n,k,j,l,t,hm,hn,hk,hj,hl,hpre,_hunit,hleft,hleft0,_h3,_h4,_h5,hray,hmark,hdelim,hbank,hcorr,hstop,hblank,hseg⟩ :=
    blank_start_variable_redispatch_with_blank_rays
  have he : zeroWord.take 20=markerWindow (List.replicate 9 0 ++ [0]) := zero_word_prefix
  have hw : Holds t (-3820) (markerWindow (List.replicate 9 0 ++ [0])) := by simpa only [he] using hpre
  have hz : ∀ i : Nat, i<3797+2 → t ((-3820:Int)+((2*9 : Nat):Int)+6+(i : Int))=false := by
    intro i hi
    apply hcorr <;> norm_num <;> omega
  obtain ⟨hnext,hwindow,hframe⟩ := variable_zero_roundtrip t (-3820) 9 3797 (by decide) hw
    (by intro q hq; exact hray q (by omega)) (by simpa using hleft0) (by simpa using hleft)
    (by simpa using hmark) (by apply hcorr <;> norm_num) (by apply hcorr <;> norm_num)
    (by apply hcorr <;> norm_num) hz (by simpa using hstop)
  let out := fillRange (setAt (-3798) t) (-3796) 3
  have hnext' : silentSegment machine (cfg 93 (-3820) t) (cfg 93 (-3820) out) 7654 := by
    norm_num at hnext ⊢
    exact hnext
  have hw' : Holds out (-3822) (markerWindow (List.replicate 10 0 ++ [1,0,3797])) := by
    change Holds out (-3822) (markerWindow (List.replicate 10 0 ++ [1,0,3797])) at hwindow
    exact hwindow
  have hbank' : Holds out 5 ((encode (List.replicate 1898 0) ++ [true,false,false]) ++ List.replicate 96 false) := by
    apply holds_transport t out _ _ hbank
    intro q hq _
    exact (hframe q (Or.inr (by norm_num; omega))).symm
  have hray' : ∀ q, q≤ -3823 → out q=false := by
    intro q hq
    exact (hframe q (Or.inl (by norm_num; omega))).trans (hray q hq)
  have hmark' : out (-3800)=true := (hframe _ (Or.inl (by norm_num))).trans hmark
  have hnext0 : out (-3799)=false := (hframe _ (Or.inl (by norm_num))).trans (hcorr _ (by norm_num) (by norm_num))
  have hzero1 : out (-3797)=false := by
    have hh := hcorr (-3797) (by norm_num) (by norm_num)
    simpa [out,fillRange,setAt] using hh
  have hstop' : out 3=true := (hframe _ (Or.inr (by norm_num))).trans hstop
  have hdelim' : out 4=false := (hframe _ (Or.inr (by norm_num))).trans hdelim
  have hright : ∀ q, 5+((encode (List.replicate 1898 0)).length : Int)+1≤q → out q=false := by
    intro q hq
    have hf : out q=t q := by
      have hh := hframe q (Or.inr (by norm_num; omega))
      dsimp only [out]
      norm_num at hh ⊢
      exact hh
    exact hf.trans (hblank q hq)
  have hall := segAdd machine _ _ _ _ 7654 hseg hnext'
  exact ⟨m,n,k,j,l,t,hm,hn,hk,hj,hl,hw',hbank',hray',hmark',hnext0,hzero1,hstop',hdelim',hright,hall⟩


#print axioms blank_start_variable_zero_roundtrip_with_blank_rays
end Shared.Beeping.NPcoNP.Bootstrap284VariableZeroBlankRays
