import Shared.Beeping.NPcoNP.Bootstrap284PostRedispatchBlankRays
import Shared.Beeping.NPcoNP.Bootstrap284PostIncrementRedispatch
import Shared.Beeping.NPcoNP.NativeZeroSelectorScan

/-! The variable-length state-261 scan on the actual blank-start execution.
This finite reachability result is not global graph refinement. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ShortScanBlankRays
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeZeroSelectorScan
open Shared.Beeping.NPcoNP.Bootstrap284PostIncrementRedispatch
open Shared.Beeping.NPcoNP.Bootstrap284PostRedispatchBlankRays
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- After the positive redispatch, the actual execution completes a further
3,825-transition silent state-261 scan and preserves its prepared bank. -/
theorem blank_start_short_zero_scan_with_blank_rays :
    ∃ (m n k j : Nat) (t : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      let out := fillRange (setAt (-3796) t) (-3794) 3
      Holds t (-3822) (zeroWord.take 24) ∧ t (-3823)=false ∧ t (-3824)=false ∧ t (-3825)=false ∧ (∀ q, q≤ -3823 → t q=false) ∧
      t (-3798)=true ∧ (∀ q, -3798<q → q<3 → t q=false) ∧ t 3=true ∧ t 4=false ∧
      Holds out 5 ((encode (List.replicate 1897 0) ++ [true,false,false]) ++ List.replicate 98 false) ∧
      (∀ q, q< -3796 ∨ 3≤q → out q=t q) ∧
      (∀ q, 5+((encode (List.replicate 1897 0)).length : Int)+1≤q → out q=false) ∧
      silentSegment machine (machine.system.run 0) (cfg 83 1 out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825) := by
  obtain ⟨m,n,k,j,t,hm,hn,hk,hj,hpre,_hunit,hleft,hleft0,h3,h4,h5,hray,hmark,hdelim,hbank,hcorr,hstop,hblank,hseg⟩ :=
    blank_start_post_increment_redispatch_with_blank_rays
  have hprefix : Holds t (-3822) (zeroWord.take 24) := by
    have hpair : Holds t (-3822) [false,true] := by
      simp only [Holds]
      exact ⟨hleft0,by simpa using hleft,trivial⟩
    have hh := holds_append_intro t (-3822) [false,true] (zeroWord.take 22) hpair (by simpa using hpre)
    have he : [false,true] ++ zeroWord.take 22=zeroWord.take 24 := by decide
    simpa only [he] using hh
  have he : zeroWord.take 22=markerWindow (List.replicate 10 0 ++ [0]) := by decide
  have hw : Holds t (-3820) (markerWindow (List.replicate 10 0 ++ [0])) := by simpa only [he] using hpre
  have hzero : ∀ i : Nat, i<3797 → t ((-3820:Int)+((2*10 : Nat):Int)+6+(i : Int))=false := by
    intro i hi
    apply hcorr <;> norm_num <;> omega
  have hnext := zero_selector_fill_return t (-3820) 10 3797 (by decide) hw
    (by simpa using hmark) (by apply hcorr <;> norm_num)
    (by apply hcorr <;> norm_num) (by apply hcorr <;> norm_num) hzero (by simpa using hstop)
  let out := fillRange (setAt (-3796) t) (-3794) 3
  have hnext' : silentSegment machine (cfg 93 (-3820) t) (cfg 83 1 out) 3825 := by
    norm_num at hnext ⊢
    exact hnext
  have hframe : ∀ q, q< -3796 ∨ 3≤q → out q=t q := by
    intro q hq
    have hn : q≠ -3796 := by omega
    have hr : ¬(-3794≤q ∧ q<3) := by omega
    simp [out,fillRange,setAt,hn,hr]
  have hbank' : Holds out 5 ((encode (List.replicate 1897 0) ++ [true,false,false]) ++ List.replicate 98 false) := by
    apply holds_transport t out _ _ hbank
    intro q hq _
    exact (hframe q (Or.inr (by omega))).symm
  have hright : ∀ q, 5+((encode (List.replicate 1897 0)).length : Int)+1≤q → out q=false := by
    intro q hq
    rw [hframe q (Or.inr (by omega))]
    exact hblank q hq
  have hall := segAdd machine _ _ _ _ 3825 hseg hnext'
  exact ⟨m,n,k,j,t,hm,hn,hk,hj,hprefix,h3,h4,h5,hray,hmark,hcorr,hstop,hdelim,hbank',hframe,hright,hall⟩


#print axioms blank_start_short_zero_scan_with_blank_rays
end Shared.Beeping.NPcoNP.Bootstrap284ShortScanBlankRays
