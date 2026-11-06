import Shared.Beeping.NPcoNP.Bootstrap284SecondBlankRay
import Shared.Beeping.NPcoNP.Bootstrap284SecondUnitWindow
import Shared.Beeping.NPcoNP.NativeAllZeroRecurrence
import Shared.Beeping.NPcoNP.NativePositiveSelectorControl
import Shared.Beeping.NPcoNP.NativeAllZeroPositiveDispatch

/-! Connect the finite all-zero recurrence to the checked blank-start tape.
This is a finite portion of the run, not the full graph/table simulation. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ReachableRecurrence
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
open Shared.Beeping.NPcoNP.NativeAllZeroRecurrence
open Shared.Beeping.NPcoNP.NativePositiveSelectorControl
open Shared.Beeping.NPcoNP.NativeAllZeroPositiveDispatch
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

/-- The checked packed snapshot contains this many alternating marker pairs.
This finite computation is kernel checked and uses the exact snapshot. -/
theorem snapshot_left_pairs_full : ∀ i : Fin 1892,
    postReturn (-39-2*(i.val : Int))=true ∧ postReturn (-40-2*(i.val : Int))=false := by
  rw [postReturn_eq]
  unfold returnedTape currentTape
  rw [run_2133586]
  decide

/-- Retain the earlier snapshot-pair interface. -/
theorem snapshot_left_pairs : ∀ i : Fin 1890,
    postReturn (-39-2*(i.val : Int))=true ∧ postReturn (-40-2*(i.val : Int))=false := by
  intro i
  exact snapshot_left_pairs_full ⟨i.val,by omega⟩

/-- The checked initial tape carries the corresponding selector window. -/
theorem return_left_window :
    Holds returnTape (-38) (markerWindow (List.replicate 13 0 ++ [0])) := by
  have hw : Holds postReturn (-38) (markerWindow (List.replicate 13 0 ++ [0])) := by
    have he : markerWindow (List.replicate 13 0 ++ [0]) =
        [false,true,false,true,false,true,false,true,false,true,false,true,false,true,
         false,true,false,true,false,true,false,true,false,true,false,true,false,true] := by decide
    rw [he,postReturn_eq]
    unfold returnedTape currentTape
    rw [run_2133586]
    simp only [Holds]
    all_goals decide
  apply holds_transport postReturn returnTape _ _ hw
  intro q _ hq
  have hl : (markerWindow (List.replicate 13 0 ++ [0])).length=28 := by decide
  rw [hl] at hq
  exact (return_left_source q (by omega)).symm

/-- The actual blank-start run reaches every stage depth supported by the
checked 1,892 alternating marker pairs, retaining the outer left tape. -/
theorem blank_start_recurrence_seed_with_frame (depth : Nat) (bound : depth≤1891) :
    ∃ (m : Nat) (out : Int → Bool), 0<m ∧
      Stage (-38) 7 0 [0,0,0] depth out ∧
      (∀ q, q< -10 → out q=returnTape q) ∧
      (∀ q, 5+((encode [0,0,0,0]).length : Int)≤q → out q=false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-38) out) (2134479+m+29) := by
  obtain ⟨e,_hs,_hh,_hw,_hm,hbank,h5,hframe,hext,_hrun,hseg⟩ :=
    blank_start_second_unit_return_with_exterior
  let before := put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true
  let tape := fillRange (setAt (-6) before) (-4) 3
  obtain ⟨hwindow,hmarker⟩ := actual_next_window e h5 hframe
  have hright : ∀ q, 12≤q → tape q=false := by
    intro q hq
    have he : e.tape q=false := (hext q (Or.inr (by omega))).trans (input_right_blank q hq)
    simpa [tape,before,fillRange,setAt,put,clearRange,
      show q≠(-6:Int) by omega,show q≠(-7:Int) by omega,show q≠(-4:Int) by omega,
      show q≠(3:Int) by omega,show ¬((-4:Int)≤q ∧ q<3) by omega,
      show ¬((-3:Int)≤q ∧ q<4) by omega] using he
  have hbankpad : Holds tape 5 (encode [1,0,0] ++ [false,false]) := by
    have htail : Holds tape (5+((encode [1,0,0]).length : Int)) [false,false] := by
      simp [encode,block,Holds,hright 12 (by omega),hright 13 (by omega)]
    exact holds_append_intro tape 5 (encode [1,0,0]) [false,false] hbank htail
  have h4input : inputTape 4=false := by
    have hw := input_scan_cells.2.2
    have h := holds_get inputTape (-4) _ hw 8 (by decide)
    simpa using h
  have h4e : e.tape 4=false := (hext 4 (Or.inl (by omega))).trans h4input
  have h2 : tape 2=true := by simp [tape,fillRange]
  have h3 : tape 3=true := by simp [tape,before,fillRange,setAt,put]
  have h4 : tape 4=false := by simp [tape,before,fillRange,setAt,put,clearRange,h4e]
  have hextension : Holds tape ((-34:Int)+((encode (List.replicate 12 0 ++ [3,5])).length : Int))
      (List.replicate 2 true ++ [false]) := by
    simpa [encode,block,List.replicate_succ,Holds] using And.intro h2 (And.intro h3 h4)
  have hbankpos : Holds tape ((-34:Int)+28+(5:Int)+(2:Int)+4)
      (encode ((0+1)::[0,0]) ++ [false,false]) := by simpa using hbankpad
  obtain ⟨m,out,hm,hmark,hblank,hbankout,hcorr,hstop,hleft,hrightout,hpositive⟩ :=
    terminal_positive_zero_control_with_right_frame tape (-34) 5 2 0 [0,0]
      (by simpa using hmarker) (by simpa using hwindow) hextension hbankpos
  have hpositive' : silentSegment machine (cfg 83 1 tape) (cfg 83 (-11) out) m := by
    simpa [encode,block,List.replicate_succ] using hpositive
  have hleft' : ∀ q, q< -10 → out q=returnTape q := by
    intro q hq
    have hleftq : out q=tape q := hleft q (by norm_num; omega)
    have htape : tape q=returnTape q := by
      have hb := hframe q (by omega)
      simpa [tape,fillRange,setAt,show q≠(-6:Int) by omega,
        show ¬((-4:Int)≤q ∧ q<3) by omega] using hb
    exact hleftq.trans htape
  have hright' : ∀ q, 12≤q → out q=false := by
    intro q hq
    have hf := hrightout q (by norm_num; omega)
    exact hf.trans (hright q hq)
  have hword : Holds out (-38) (markerWindow (List.replicate 13 0 ++ [0])) := by
    apply holds_transport returnTape out _ _ return_left_window
    intro q _ hq
    have hl : (markerWindow (List.replicate 13 0 ++ [0])).length=28 := by decide
    rw [hl] at hq
    exact (hleft' q (by omega)).symm
  have hleftpairs : ∀ i : Nat, i<depth+1 → out ((-38:Int)-2*(i : Int)-1)=true ∧
      out ((-38:Int)-2*(i : Int)-2)=false := by
    intro i hi
    have h := snapshot_left_pairs_full ⟨i,by omega⟩
    have hq1 : (-38:Int)-2*(i : Int)-1< -10 := by omega
    have hq2 : (-38:Int)-2*(i : Int)-2< -10 := by omega
    rw [hleft' _ hq1,hleft' _ hq2,return_left_source _ (by omega),return_left_source _ (by omega)]
    have hp1 : (-38:Int)-2*(i : Int)-1= -39-2*(i : Int) := by omega
    have hp2 : (-38:Int)-2*(i : Int)-2= -40-2*(i : Int) := by omega
    simpa only [hp1,hp2] using h
  have hzero4 : Holds out 5 (encode [0,0,0,0]) := by
    have ht : Holds out 5 (encode [0,0,0,0] ++ [false]) := by simpa [encode,block] using hbankout
    exact Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue.holds_prefix_word out 5 _ [false] ht
  have hpadding : Holds out (5+((encode [0,0,0,0]).length : Int)) (List.replicate (2*depth+3) false) := by
    apply holds_of_get
    intro i hi
    have hp : 12≤5+((encode [0,0,0,0]).length : Int)+(i : Int) := by
      simp [encode,block]; omega
    simpa only [List.getElem_replicate] using hright' _ hp
  have hfull := holds_append_intro out 5 (encode [0,0,0,0])
    (List.replicate (2*depth+3) false) hzero4 hpadding
  have hstage : Stage (-38) 7 0 [0,0,0] depth out := by
    refine ⟨hword,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro i hi; exact hleftpairs i (by omega)
    · simpa using hmark
    · apply hcorr <;> norm_num
    · apply hcorr <;> norm_num
    · apply hcorr <;> norm_num
    · intro i hi
      apply hcorr <;> norm_num <;> omega
    · simpa using hstop
    · simpa using hblank
    · simpa using hfull
  have hdispatch := marker_window_to93 out (-38) (List.replicate 13 0 ++ [0])
    (by decide) hword (by simpa using (hleftpairs 0 (by omega)).1)
  have hdispatch' : silentSegment machine (cfg 83 (-11) out) (cfg 93 (-38) out) 29 := by
    simpa [encode,block,List.replicate_succ] using hdispatch
  have hfirst := segAdd machine _ _ _ 2134479 m hseg hpositive'
  have hall := segAdd machine _ _ _ (2134479+m) 29 hfirst hdispatch'
  exact ⟨m,out,hm,hstage,hleft',by intro q hq; apply hright'; simp [encode,block] at hq; omega,hall⟩

/-- Retain the earlier concrete seed interface. -/
theorem blank_start_recurrence_seed :
    ∃ (m : Nat) (out : Int → Bool), 0<m ∧
      Stage (-38) 7 0 [0,0,0] 1889 out ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-38) out) (2134479+m+29) := by
  obtain ⟨m,out,hm,hstage,_hframe,_hright,hseg⟩ := blank_start_recurrence_seed_with_frame 1889 (by omega)
  exact ⟨m,out,hm,hstage,hseg⟩

/-- From blank start, the checked machine completes 1,889 successive silent
cycles, moving the anchor to -3816 and extending the bank by 1,889 zeros. -/
theorem blank_start_1889_cycles :
    ∃ (m n : Nat) (out : Int → Bool), 0<m ∧ 1889≤n ∧
      Stage (-3816) 3785 0 (List.replicate 1892 0) 0 out ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3816) out) (2134479+m+29+n) := by
  obtain ⟨m,seed,hm,hstage,hstart⟩ := blank_start_recurrence_seed
  obtain ⟨n,out,hn,hcycles,hfinal⟩ := stage_iterate 1889 (-38) 7 0 [0,0,0] seed hstage
  have hvalues : [0,0,0] ++ List.replicate 1889 0=List.replicate 1892 0 := by decide
  norm_num only [Nat.cast_ofNat] at hcycles hfinal
  rw [hvalues] at hfinal
  have hall := segAdd machine _ _ _ (2134479+m+29) n hstart hcycles
  exact ⟨m,n,out,hm,hn,hfinal,hall⟩

/-- The third cell beyond the last checked marker is also blank. -/
theorem snapshot_after_markers_extra : returnTape (-3825)=false := by
  rw [return_left_source (-3825) (by omega),postReturn_eq]
  unfold returnedTape currentTape
  rw [run_2133586]
  decide

/-- The two cells immediately beyond the last checked marker are blank. -/
theorem snapshot_after_markers : returnTape (-3823)=false ∧ returnTape (-3824)=false := by
  rw [return_left_source (-3823) (by omega),return_left_source (-3824) (by omega),postReturn_eq]
  unfold returnedTape currentTape
  rw [run_2133586]
  decide

/-- Exhaust all 1,891 marker-present cycles and expose the absent-marker
boundary on the literal blank-start execution. -/
theorem blank_start_marker_runway_end_with_extra :
    ∃ (m n : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧
      Stage (-3820) 3789 0 (List.replicate 1894 0) 0 out ∧
      out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      (∀ q, 5+((encode (List.replicate 1895 0)).length : Int)≤q → out q=false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out) (2134479+m+29+n) := by
  obtain ⟨m,seed,hm,hstage,hseedframe,hseedblank,hstart⟩ := blank_start_recurrence_seed_with_frame 1891 (by omega)
  obtain ⟨n,out,hn,hcycles,hfinal,hframe,hblank⟩ :=
    stage_iterate_with_blank_ray 1891 (-38) 7 0 [0,0,0] seed hstage (by simpa using hseedblank)
  have hvalues : [0,0,0] ++ List.replicate 1891 0=List.replicate 1894 0 := by decide
  norm_num only [Nat.cast_ofNat] at hcycles hfinal hframe hblank
  rw [hvalues] at hfinal hblank
  have hbankvalues : 0::List.replicate 1894 0=List.replicate 1895 0 := by decide
  rw [hbankvalues] at hblank
  have hblank3 : out (-3823)=false := by
    rw [hframe _ (by omega),hseedframe _ (by omega)]
    exact snapshot_after_markers.1
  have hblank4 : out (-3824)=false := by
    rw [hframe _ (by omega),hseedframe _ (by omega)]
    exact snapshot_after_markers.2
  have hblank5 : out (-3825)=false := by
    rw [hframe _ (by omega),hseedframe _ (by omega)]
    exact snapshot_after_markers_extra
  have hall := segAdd machine _ _ _ (2134479+m+29) n hstart hcycles
  exact ⟨m,n,out,hm,hn,hfinal,hblank3,hblank4,hblank5,by simpa using hblank,hall⟩

/-- Retain the earlier runway-end interface. -/
theorem blank_start_marker_runway_end :
    ∃ (m n : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧
      Stage (-3820) 3789 0 (List.replicate 1894 0) 0 out ∧
      out (-3823)=false ∧ out (-3824)=false ∧
      (∀ q, 5+((encode (List.replicate 1895 0)).length : Int)≤q → out q=false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out) (2134479+m+29+n) := by
  obtain ⟨m,n,out,hm,hn,hs,h3,h4,_h5,hblank,hseg⟩ := blank_start_marker_runway_end_with_extra
  exact ⟨m,n,out,hm,hn,hs,h3,h4,hblank,hseg⟩

/-- The actual blank-start execution takes the absent-marker branch after
the full marker runway, preserving a bank with 1,897 zero-valued entries. -/
theorem blank_start_after_marker_absence_with_extra :
    ∃ (m n k : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧
      Holds out 5 (encode (List.replicate 1897 0) ++ List.replicate 101 false) ∧
      Holds out (-3820) (zeroWord.take 24) ∧
      out (-3821)=true ∧ out (-3822)=false ∧ out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      out (-3796)=true ∧ (∀ q, -3796<q → q<3 → out q=false) ∧ out 3=true ∧ out 4=false ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)) := by
  obtain ⟨m,n,t,hm,hn,stage,habsent,hbefore,hextra,hblank,hstart⟩ := blank_start_marker_runway_end_with_extra
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
  obtain ⟨k,out,hk,hresult,hmark,hdelim,hcorr,hstop,hframe,_hleft,hnext⟩ :=
    padded_absent_positive_dispatch_with_control (-3820) 3789 0 (List.replicate 1894 0)
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
  have hlast : silentSegment machine (cfg 93 (-3820) t) (cfg 93 (-3820) out) (k+31) :=
    hnext hbefore
  have hall := segAdd machine _ _ _ (2134479+m+29+n) (k+31) hstart hlast
  exact ⟨m,n,k,out,hm,hn,hk,hresult',hprefix,ho1,ho2,ho3,ho4,ho5,
    by simpa using hmark,by simpa using hcorr,by simpa using hstop,by simpa using hdelim,hall⟩

/-- Retain the earlier post-absence control interface. -/
theorem blank_start_after_marker_absence_with_control :
    ∃ (m n k : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧
      Holds out 5 (encode (List.replicate 1897 0) ++ List.replicate 101 false) ∧
      Holds out (-3820) (zeroWord.take 24) ∧
      out (-3821)=true ∧ out (-3822)=false ∧ out (-3823)=false ∧ out (-3824)=false ∧
      out (-3796)=true ∧ (∀ q, -3796<q → q<3 → out q=false) ∧ out 3=true ∧ out 4=false ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)) := by
  obtain ⟨m,n,k,out,hm,hn,hk,hbank,hpre,h1,h2,h3,h4,_h5,hmark,hcorr,hstop,hdelim,hseg⟩ :=
    blank_start_after_marker_absence_with_extra
  exact ⟨m,n,k,out,hm,hn,hk,hbank,hpre,h1,h2,h3,h4,hmark,hcorr,hstop,hdelim,hseg⟩

/-- Retain the earlier post-absence interface. -/
theorem blank_start_after_marker_absence :
    ∃ (m n k : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧
      Holds out 5 (encode (List.replicate 1897 0) ++ [false]) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)) := by
  obtain ⟨m,n,k,out,hm,hn,hk,hbank,_hp,_h1,_h2,_h3,_h4,_hmark,_hcorr,_hstop,_hdelim,hseg⟩ :=
    blank_start_after_marker_absence_with_control
  have hsplit : List.replicate 101 false=[false] ++ List.replicate 100 false := by decide
  rw [hsplit,←List.append_assoc] at hbank
  have hbank' := Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue.holds_prefix_word
    out 5 (encode (List.replicate 1897 0) ++ [false]) (List.replicate 100 false) hbank
  exact ⟨m,n,k,out,hm,hn,hk,hbank',hseg⟩

#print axioms snapshot_left_pairs
#print axioms snapshot_left_pairs_full
#print axioms return_left_window
#print axioms blank_start_recurrence_seed
#print axioms blank_start_recurrence_seed_with_frame
#print axioms blank_start_1889_cycles
#print axioms snapshot_after_markers
#print axioms blank_start_marker_runway_end
#print axioms blank_start_after_marker_absence
#print axioms blank_start_after_marker_absence_with_control
end Shared.Beeping.NPcoNP.Bootstrap284ReachableRecurrence
