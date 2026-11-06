import Shared.Beeping.NPcoNP.Bootstrap284PostAbsenceLeftRay
import Shared.Beeping.NPcoNP.NativeAbsentDispatchRightFrame
import Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
import Shared.Beeping.NPcoNP.Bootstrap284SnapshotLeftBlank
import Shared.Beeping.NPcoNP.Bootstrap284SecondUnitWindow
import Shared.Beeping.NPcoNP.NativeAllZeroRecurrence
import Shared.Beeping.NPcoNP.NativePositiveSelectorControl
import Shared.Beeping.NPcoNP.NativeAllZeroPositiveDispatch

/-! Connect the finite all-zero recurrence to the checked blank-start tape.
This is a finite portion of the run, not the full graph/table simulation. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PostAbsenceBlankRays
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.Bootstrap284SnapshotLeftBlank
open Shared.Beeping.NPcoNP.NativeAllZeroRecurrence
open Shared.Beeping.NPcoNP.NativePositiveSelectorControl
open Shared.Beeping.NPcoNP.NativeAllZeroPositiveDispatch
open Shared.Beeping.NPcoNP.NativeAbsentDispatchRightFrame
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.Bootstrap284SecondDispatch
open Shared.Beeping.NPcoNP.Bootstrap284SecondReturnTimed
open Shared.Beeping.NPcoNP.Bootstrap284TerminalUnit
open Shared.Beeping.NPcoNP.Bootstrap284NextReturnExact
open Shared.Beeping.NPcoNP.Bootstrap284NextSelectorExact
open Shared.Beeping.NPcoNP.Bootstrap284SecondIncrementReturn
open Shared.Beeping.NPcoNP.Bootstrap284SecondBlankRay
open Shared.Beeping.NPcoNP.Bootstrap284SecondUnitReturn
open Shared.Beeping.NPcoNP.Bootstrap284SecondUnitWindow
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

/-! Preserve the unbounded left blank ray through the absent-marker path. -/
theorem blank_start_after_marker_absence_with_blank_rays :
    ∃ (m n k : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧
      Holds out 5 (encode (List.replicate 1897 0) ++ List.replicate 101 false) ∧
      Holds out (-3820) (zeroWord.take 24) ∧
      out (-3821)=true ∧ out (-3822)=false ∧ out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      (∀ q, q≤ -3823 → out q=false) ∧
      out (-3796)=true ∧ (∀ q, -3796<q → q<3 → out q=false) ∧ out 3=true ∧ out 4=false ∧
      (∀ q, 5+((encode (List.replicate 1897 0)).length : Int)≤q → out q=false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)) := by
  obtain ⟨m,n,t,hm,hn,stage,hleftblank,hblank,hstart⟩ := blank_start_runway_end_with_left_ray
  have habsent : t (-3823)=false := hleftblank _ (by norm_num)
  have hbefore : t (-3824)=false := hleftblank _ (by norm_num)
  have hextra : t (-3825)=false := hleftblank _ (by norm_num)
  have hvalues : 0::List.replicate 1894 0=List.replicate 1895 0 := by decide
  have hlen : (encode (0::List.replicate 1894 0)).length=3790 := by
    rw [hvalues,zeros_length]
  have hbank3 : Holds t 5 (encode (0::List.replicate 1894 0) ++ [false,false,false]) := by
    simpa using stage.bank
  have htail : Holds t (5+((encode (0::List.replicate 1894 0) ++ [false,false,false]).length : Int))
      ([false,false] ++ List.replicate 100 false) := by
    have hp : 5+((encode (0::List.replicate 1894 0) ++ [false,false,false]).length : Int)=3798 := by
      simp only [List.length_append,List.length_cons,List.length_nil,hlen]
      norm_num
    rw [hp]
    have hw : [false,false] ++ List.replicate 100 false=List.replicate 102 false := by decide
    rw [hw]
    apply holds_of_get
    intro i hi
    have hq : 5+((encode (List.replicate 1895 0)).length : Int)≤3798+(i : Int) := by
      rw [←hvalues,hlen]
      omega
    simpa only [List.getElem_replicate] using hblank _ hq
  have hbank5 := holds_append_intro t 5 (encode (0::List.replicate 1894 0) ++ [false,false,false])
    ([false,false] ++ List.replicate 100 false) hbank3 htail
  have hbank : Holds t ((-3820:Int)+36+(3789:Int))
      ((encode (0::List.replicate 1894 0) ++ [false,false,false]) ++
        ([false,false] ++ List.replicate 100 false)) := by
    simpa using hbank5
  have hleft0 : t ((-3820:Int)-2)=false := by simpa using (stage.left 0 (by omega)).2
  have hearlier : t ((-3820:Int)-1)=true := by simpa using (stage.left 0 (by omega)).1
  obtain ⟨k,out,hk,hresult,hmark,hdelim,hcorr,hstop,hframe,hfar,_hleft,hnext⟩ :=
    padded_absent_positive_dispatch_with_right_frame (-3820) 3789 0 (List.replicate 1894 0)
      (List.replicate 100 false) t
      stage.window hleft0 hearlier habsent stage.marker stage.nextZero stage.firstZero stage.secondZero
      stage.zeros stage.stop stage.delimiter hbank
  have hvals : 0::(List.replicate 1894 0 ++ [0,0])=List.replicate 1897 0 := by decide
  have hresult' : Holds out 5 (encode (List.replicate 1897 0) ++ List.replicate 101 false) := by
    simpa [hvals,List.replicate_succ,List.append_assoc] using hresult
  have hprefix : Holds out (-3820) (zeroWord.take 24) := by
    have hpref : Holds t (-3820) (zeroWord.take 24) := by
      apply Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue.holds_prefix_word
        t (-3820) (zeroWord.take 24) (zeroWord.drop 24)
      simpa [zeroWord] using stage.window
    apply holds_transport t out _ _ hpref
    intro q _ hq
    have hl : (zeroWord.take 24).length=24 := by decide
    rw [hl] at hq
    exact (hframe q (by omega)).symm
  have ho1 : out (-3821)=true := (hframe _ (by norm_num)).trans (by simpa using hearlier)
  have ho2 : out (-3822)=false := (hframe _ (by norm_num)).trans (by simpa using hleft0)
  have ho3 : out (-3823)=false := (hframe _ (by norm_num)).trans habsent
  have ho4 : out (-3824)=false := (hframe _ (by norm_num)).trans hbefore
  have ho5 : out (-3825)=false := (hframe _ (by norm_num)).trans hextra
  have hray : ∀ q, q≤ -3823 → out q=false := by
    intro q hq
    rw [hframe q (by omega)]
    exact hleftblank q hq
  have hbanklen : (encode (List.replicate 1897 0)).length=3794 := by
    rw [zeros_length]
  have hzero : out 3799=false := by
    have hh := holds_split out 5 (encode (List.replicate 1897 0)) (List.replicate 101 false) hresult'
    rw [hbanklen] at hh
    simpa [Holds] using hh.2.1
  have hright : ∀ q, 5+((encode (List.replicate 1897 0)).length : Int)≤q → out q=false := by
    intro q hq
    rw [hbanklen] at hq
    by_cases he : q=3799
    · simpa [he] using hzero
    · have hcut : (-3820:Int)+36+(3789:Int)+
          (((encode (0::List.replicate 1894 0) ++ [false,false,false]) ++ [false,false]).length : Int)≤q := by
        simp only [List.length_append,List.length_cons,List.length_nil,hlen]
        omega
      rw [hfar q hcut]
      apply hblank
      rw [←hvalues,hlen]
      omega
  have hlast : silentSegment machine (cfg 93 (-3820) t) (cfg 93 (-3820) out) (k+31) :=
    hnext hbefore
  have hall := segAdd machine _ _ _ (2134479+m+29+n) (k+31) hstart hlast
  exact ⟨m,n,k,out,hm,hn,hk,hresult',hprefix,ho1,ho2,ho3,ho4,ho5,hray,
    by simpa using hmark,by simpa using hcorr,by simpa using hstop,by simpa using hdelim,hright,hall⟩


#print axioms blank_start_after_marker_absence_with_blank_rays
end Shared.Beeping.NPcoNP.Bootstrap284PostAbsenceBlankRays
