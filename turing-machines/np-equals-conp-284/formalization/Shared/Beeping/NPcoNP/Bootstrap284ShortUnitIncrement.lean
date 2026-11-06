import Shared.Beeping.NPcoNP.Bootstrap284ShortZeroReturn
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
import Shared.Beeping.NPcoNP.NativeUnitSelectorBankIncrement
import Shared.Beeping.NPcoNP.NativeUnitIncrementPadding

/-! The next shortened unit selector reaches and increments the actual bank. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ShortUnitIncrement
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
open Shared.Beeping.NPcoNP.NativeUnitIncrementPadding
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284ShortZeroReturn
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- The actual shorter unit selector completes its bank increment in 7,622
further silent transitions, incrementing the first of 1,898 zero values. -/
theorem blank_start_short_unit_increment_with_left_ray :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      e.state=23 ∧ e.head=3800 ∧
      Holds e.tape 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) ∧
      Holds e.tape (-3822) (zeroWord.take 24) ∧
      e.tape (-3823)=false ∧ e.tape (-3824)=false ∧ e.tape (-3825)=false ∧
      (∀ q, q≤ -3823 → e.tape q=false) ∧ e.tape (-3798)=true ∧
      e.tape (-3797)=false ∧ e.tape (-3796)=false ∧ e.tape (-3795)=false ∧
      Holds e.tape (-3794) (List.replicate 3798 true ++ [false]) ∧
      silentSegment machine (machine.system.run 0) e
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622) := by
  obtain ⟨m,n,k,j,t,hm,hn,hk,hj,hwindow,hl3,hl4,hl5,hray,hlmark,hz7,hz5,h2,h3,h4,hbank,hseg⟩ :=
    blank_start_short_zero_return_with_left_ray
  let out := fillRange (setAt (-3796) t) (-3794) 3
  let selected := clearAt (-3796) out
  have hprefixout : Holds out (-3822) (zeroWord.take 24) := by
    have hh := holds_prefix_word out (-3822)
      ((markerWindow (List.replicate 11 0 ++ [1,0,3795])).take 24)
      ((markerWindow (List.replicate 11 0 ++ [1,0,3795])).drop 24) (by
        simpa only [List.take_append_drop] using hwindow)
    have he : (markerWindow (List.replicate 11 0 ++ [1,0,3795])).take 24=zeroWord.take 24 := by decide
    simpa only [he] using hh
  have hsplit : markerWindow (List.replicate 11 0 ++ [1,0,3795]) =
      [false,true] ++ markerWindow (List.replicate 10 0 ++ [1,0,3795]) := by decide
  rw [hsplit] at hwindow
  have htail := holds_append_tail out (-3822) [false,true]
    (markerWindow (List.replicate 10 0 ++ [1,0,3795])) hwindow
  have hw : Holds out (-3820) (markerWindow (List.replicate 10 0 ++ 1::0::3795::[])) := by simpa using htail
  have hrun0 : Holds selected (-3794) (List.replicate 3797 true) := by
    apply holds_of_get
    intro i hi
    have hi' : i<3797 := by simpa using hi
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
    have hh := holds_append_intro selected (-3794) (List.replicate 3797 true) [true,false] hrun0 (by simpa using hpair)
    have he : List.replicate 3797 true ++ [true,false]=List.replicate 3798 true ++ [false] := by
      rw [show 3798=3797+1 by decide,List.replicate_succ']
      simp [List.append_assoc]
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
    simp [List.append_assoc]
  have hbank' : Holds out 5 (encode (0::List.replicate 1897 0) ++ [false]) := by
    rw [hbankword]
    exact holds_prefix_word out 5 (encode (List.replicate 1897 0) ++ [true,false,false])
      (List.replicate 98 false) hbank
  obtain ⟨e,hs,hh,hebank,hleft,hframe,hinc⟩ :=
    unit_selector_bank_increment_with_control out (-3820) 10 0 3795 3798 0 []
      (List.replicate 1897 0) hw (by simpa using hword0) (by simpa using hbank')
  have hlen : (encode (List.replicate 1897 0)).length=3794 := by rw [zeros_length]
  have hh' : e.head=3800 := by
    norm_num [hlen] at hh ⊢
    exact hh
  have hleft' : ∀ q, q<5 → e.tape q=selected q := by
    intro q hq
    apply hleft
    norm_num
    exact hq
  have hepre : Holds e.tape (-3822) (zeroWord.take 24) := by
    apply holds_transport out e.tape _ _ hprefixout
    intro q hq hq'
    have hl : (zeroWord.take 24).length=24 := by decide
    rw [hl] at hq'
    rw [hleft' q (by omega)]
    simp [selected,clearAt,show q≠ -3796 by omega]
  have heray : ∀ q, q≤ -3823 → e.tape q=false := by
    intro q hq
    rw [hleft' q (by omega)]
    simpa [selected,clearAt,show q≠ -3796 by omega] using hray q hq
  have he3 : e.tape (-3823)=false := by
    rw [hleft' _ (by norm_num)]
    simpa [selected,clearAt] using hl3
  have he4 : e.tape (-3824)=false := by
    rw [hleft' _ (by norm_num)]
    simpa [selected,clearAt] using hl4
  have he5 : e.tape (-3825)=false := by
    rw [hleft' _ (by norm_num)]
    simpa [selected,clearAt] using hl5
  have hbankpad : Holds out 5 ((encode (0::List.replicate 1897 0) ++ [false]) ++ List.replicate 98 false) := by
    rw [hbankword]
    exact hbank
  have hright : ∀ q, 5+(((0+1)+(encode (List.replicate 1897 0)).length : Nat):Int)<q → e.tape q=out q := by
    intro q hq
    have hq' : (3800:Int)<q := by norm_num [hlen] at hq; omega
    apply hframe q
    · norm_num; omega
    · right
      simp only [hlen]
      norm_num
      exact hq'
  have hbankfull : Holds e.tape 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) := by
    have hh := unit_increment_padding out e.tape 5 0 (List.replicate 1897 0) (List.replicate 98 false)
      hbankpad (by simpa using hebank) hright
    exact hh
  have hemark : e.tape (-3798)=true := by
    rw [hleft' _ (by norm_num)]
    simpa [selected,clearAt] using hlmark
  have he7 : e.tape (-3797)=false := by
    rw [hleft' _ (by norm_num)]
    simpa [selected,clearAt] using hz7
  have he0 : e.tape (-3796)=false := by
    rw [hleft' _ (by norm_num)]
    simp [selected,clearAt]
  have he1 : e.tape (-3795)=false := by
    rw [hleft' _ (by norm_num)]
    simpa [selected,clearAt] using hz5
  have herun : Holds e.tape (-3794) (List.replicate 3798 true ++ [false]) := by
    apply holds_transport selected e.tape _ _ hword
    intro q _ hq
    symm
    apply hleft'
    simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil] at hq
    omega
  have hinc' : silentSegment machine (cfg 93 (-3820) out) e 7622 := by
    norm_num [hlen] at hinc ⊢
    exact hinc
  have hall := segAdd machine _ _ _ _ 7622 hseg hinc'

  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hh',hbankfull,hepre,he3,he4,he5,heray,hemark,he7,he0,he1,herun,hall⟩

/-- Retain the earlier marker-control increment interface. -/
theorem blank_start_short_unit_increment_with_marker :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      e.state=23 ∧ e.head=3800 ∧
      Holds e.tape 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) ∧
      Holds e.tape (-3822) (zeroWord.take 24) ∧
      e.tape (-3823)=false ∧ e.tape (-3824)=false ∧ e.tape (-3825)=false ∧ e.tape (-3798)=true ∧
      e.tape (-3797)=false ∧ e.tape (-3796)=false ∧ e.tape (-3795)=false ∧
      Holds e.tape (-3794) (List.replicate 3798 true ++ [false]) ∧
      silentSegment machine (machine.system.run 0) e
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hh,hbank,hpre,h3,h4,h5,_hray,hmark,h7,h0,h1,hrun,hseg⟩ :=
    blank_start_short_unit_increment_with_left_ray
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hh,hbank,hpre,h3,h4,h5,hmark,h7,h0,h1,hrun,hseg⟩

/-- Retain the earlier framed increment interface. -/
theorem blank_start_short_unit_increment_with_frames :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      e.state=23 ∧ e.head=3800 ∧
      Holds e.tape 5 (encode (1::List.replicate 1897 0) ++ List.replicate 98 false) ∧
      Holds e.tape (-3822) (zeroWord.take 24) ∧
      e.tape (-3823)=false ∧ e.tape (-3824)=false ∧ e.tape (-3825)=false ∧
      e.tape (-3797)=false ∧ e.tape (-3796)=false ∧ e.tape (-3795)=false ∧
      Holds e.tape (-3794) (List.replicate 3798 true ++ [false]) ∧
      silentSegment machine (machine.system.run 0) e
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hh,hbank,hpre,h3,h4,h5,_hmk,h7,h0,h1,hrun,hseg⟩ :=
    blank_start_short_unit_increment_with_marker
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hh,hbank,hpre,h3,h4,h5,h7,h0,h1,hrun,hseg⟩

/-- Retain the earlier reachable carry-input interface. -/
theorem blank_start_short_unit_increment_with_carry :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      e.state=23 ∧ e.head=3800 ∧ Holds e.tape 5 (encode (1::List.replicate 1897 0)) ∧
      e.tape (-3797)=false ∧ e.tape (-3796)=false ∧ e.tape (-3795)=false ∧
      Holds e.tape (-3794) (List.replicate 3798 true ++ [false]) ∧
      silentSegment machine (machine.system.run 0) e
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hh,hbank,_hp,_h3,_h4,_h5,h7,h0,h1,hrun,hseg⟩ :=
    blank_start_short_unit_increment_with_frames
  have hb := holds_prefix_word e.tape 5 (encode (1::List.replicate 1897 0)) (List.replicate 98 false) hbank
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hh,hb,h7,h0,h1,hrun,hseg⟩

/-- Retain the earlier reachable increment control interface. -/
theorem blank_start_short_unit_increment_with_control :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      e.state=23 ∧ e.head=3800 ∧ Holds e.tape 5 (encode (1::List.replicate 1897 0)) ∧
      e.tape (-3796)=false ∧ e.tape (-3795)=false ∧
      Holds e.tape (-3794) (List.replicate 3798 true ++ [false]) ∧
      silentSegment machine (machine.system.run 0) e
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hh,hbank,_h7,h0,h1,hrun,hseg⟩ :=
    blank_start_short_unit_increment_with_carry
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hh,hbank,h0,h1,hrun,hseg⟩

/-- Retain the earlier reachable unit-increment interface. -/
theorem blank_start_short_unit_increment :
    ∃ (m n k j : Nat) (e : Config 284), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      e.state=23 ∧ e.head=3800 ∧ Holds e.tape 5 (encode (1::List.replicate 1897 0)) ∧
      silentSegment machine (machine.system.run 0) e
        (2134479+m+29+n+(k+31)+30492+7652+j+31+3825+3827+7622) := by
  obtain ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hh,hbank,_h0,_h1,_hrun,hseg⟩ :=
    blank_start_short_unit_increment_with_control
  exact ⟨m,n,k,j,e,hm,hn,hk,hj,hs,hh,hbank,hseg⟩

#print axioms blank_start_short_unit_increment
end Shared.Beeping.NPcoNP.Bootstrap284ShortUnitIncrement
