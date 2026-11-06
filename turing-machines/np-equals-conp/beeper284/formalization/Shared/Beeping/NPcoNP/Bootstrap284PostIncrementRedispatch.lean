import Shared.Beeping.NPcoNP.Bootstrap284PostIncrementPositiveScan
import Shared.Beeping.NPcoNP.NativePositiveSelectorDirect
import Shared.Beeping.NPcoNP.NativePositiveShortDispatch
import Shared.Beeping.NPcoNP.NativePositiveBankPadding

/-! The following short redispatch is reached from the blank tape.
This finite execution is not a full graph/table simulation. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PostIncrementRedispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank

open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeManyTerminalWindow
open Shared.Beeping.NPcoNP.NativePositiveSelectorControl
open Shared.Beeping.NPcoNP.NativePositiveSelectorDirect
open Shared.Beeping.NPcoNP.NativePositiveShortDispatch
open Shared.Beeping.NPcoNP.NativePositiveBankPadding
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.Bootstrap284PostIncrementPositiveScan
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- The actual positive selector returns to state 93 after a further 31
silent transitions. Earlier durations remain existential. -/
theorem blank_start_post_increment_redispatch_with_left_ray :
    ∃ (m n k j : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      Holds out (-3820) (zeroWord.take 22) ∧
      Holds out (-3820) (markerWindow (List.replicate 10 0 ++ [1])) ∧ out (-3821)=true ∧ out (-3822)=false ∧
      out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      (∀ q, q≤ -3823 → out q=false) ∧
      out (-3798)=true ∧ out 4=false ∧
      Holds out 5 ((encode (List.replicate 1897 0) ++ [true,false,false]) ++ List.replicate 98 false) ∧
      (∀ q, -3798<q → q<3 → out q=false) ∧ out 3=true ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31) := by
  obtain ⟨m,n,k,e,hm,hn,hk,_hs,hbank,hwindow,hleft3,hleft4,hleft5,hray,h2,h3,h4,hseg⟩ :=
    blank_start_post_increment_roundtrip_with_left_ray
  let t := Shared.Beeping.NPcoNP.NativePostAbsenceUnitScan.scanOutput (-3820) 3789
    (Shared.Beeping.NPcoNP.NativeHalfSweep.put
      (Shared.Beeping.NPcoNP.NativeHalfState28Exact.clearRange
        (Shared.Beeping.NPcoNP.NativeHalfSweep.put (Shared.Beeping.NPcoNP.NativeHalfSweep.put e.tape (-3795) true) (-3792) false) (-3791) 4) 3 true)
  have hprefix : Holds t (-3822) (zeroWord.take 24) := by
    have hh := holds_prefix_word t (-3822)
      ((markerWindow (List.replicate 12 0 ++ [3,3793])).take 24)
      ((markerWindow (List.replicate 12 0 ++ [3,3793])).drop 24) (by
        simpa only [List.take_append_drop] using hwindow)
    have he : (markerWindow (List.replicate 12 0 ++ [3,3793])).take 24=zeroWord.take 24 := by decide
    simpa only [he] using hh
  have hsplit : markerWindow (List.replicate 12 0 ++ [3,3793]) =
      [false,true] ++ markerWindow (List.replicate 11 0 ++ [3,3793]) := by decide
  have hcarry := selector_carry t (-3822) 3793 hwindow
  rw [hsplit] at hwindow
  have htail := holds_append_tail t (-3822) [false,true]
    (markerWindow (List.replicate 11 0 ++ [3,3793])) hwindow
  have hw : Holds t (-3820) (markerWindow (List.replicate 11 0 ++ [0+3,3793])) := by
    simpa using htail
  have hlen : (encode (List.replicate 11 0 ++ [0+3,3793])).length=3822 := by
    simp [encode,block_length]
  have hext : Holds t ((-3820:Int)+((encode (List.replicate 11 0 ++ [0+3,3793])).length : Int))
      (List.replicate 2 true ++ [false]) := by
    rw [hlen]
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds]
    norm_num
    exact ⟨h2,h3,h4⟩
  have hrep : List.replicate 100 false=[false,false] ++ List.replicate 98 false := by decide
  have hb : Holds t ((-3820:Int)+((2*11 : Nat):Int)+4+(0:Int)+(3793:Int)+(2:Int)+4)
      (encode ((0+1)::List.replicate 1896 0) ++ [false,false]) := by
    rw [hrep,←List.append_assoc] at hbank
    have hh := holds_prefix_word t 5 (encode (1::List.replicate 1896 0) ++ [false,false])
      (List.replicate 98 false) hbank
    simpa using hh
  have hc : downHolds t ((-3820:Int)+((2*11 : Nat):Int)+3)
      (List.replicate 3 true ++ [false]) := by simpa using hcarry
  obtain ⟨j,out,hj,hmark,hblank,hresult,hcorr,hstop,hleft,hright,hbody⟩ :=
    terminal_positive_direct_control t (-3820) 11 3793 2 0 (List.replicate 1896 0)
      hw hext (by simpa using hb) hc
  have hbody' : silentSegment machine (cfg 93 (-3820) t) (cfg 83 (-3799) out) j := by
    simpa using hbody
  have hresult' : Holds out 5 (encode (List.replicate 1897 0) ++ [true,false,false]) := by
    simpa [List.replicate_succ] using hresult
  have hprefixout : Holds out (-3822) (zeroWord.take 24) := by
    apply holds_transport t out _ _ hprefix
    intro q _ hq
    have hl : (zeroWord.take 24).length=24 := by decide
    rw [hl] at hq
    exact (hleft q (by omega)).symm
  have hwords : zeroWord.take 24=[false,true] ++ zeroWord.take 22 := by decide
  have hsmall : Holds out (-3820) (zeroWord.take 22) := by
    rw [hwords] at hprefixout
    have hh := holds_append_tail out (-3822) [false,true] (zeroWord.take 22) hprefixout
    simpa using hh
  have hunit : Holds out (-3820) (markerWindow (List.replicate 10 0 ++ [1])) := by
    have hm : Holds out (-3798) [true] := by simpa [Holds] using hmark
    have hh := holds_append_intro out (-3820) (zeroWord.take 22) [true] hsmall (by
      have hl : (zeroWord.take 22).length=22 := by decide
      simpa [hl] using hm)
    have he : zeroWord.take 22 ++ [true]=markerWindow (List.replicate 10 0 ++ [1]) := by decide
    simpa only [he] using hh
  have hhead0 : out (-3822)=false := by
    have hh := holds_get t (-3822) (zeroWord.take 24) hprefix 0 (by decide)
    have hv : (zeroWord.take 24)[0]=false := by decide
    rw [hv] at hh
    simpa using (hleft (-3822) (by norm_num)).trans (by simpa using hh)
  have hhead1 : out (-3821)=true := by
    have hh := holds_get t (-3822) (zeroWord.take 24) hprefix 1 (by decide)
    have hv : (zeroWord.take 24)[1]=true := by decide
    rw [hv] at hh
    simpa using (hleft (-3821) (by norm_num)).trans (by simpa using hh)
  have hray' : ∀ q, q≤ -3823 → out q=false := by
    intro q hq
    exact (hleft q (by omega)).trans (hray q hq)
  have hl3 : out (-3823)=false := (hleft _ (by norm_num)).trans hleft3
  have hl4 : out (-3824)=false := (hleft _ (by norm_num)).trans hleft4
  have hl5 : out (-3825)=false := (hleft _ (by norm_num)).trans hleft5
  have hbankpad : Holds t 5 ((encode (1::List.replicate 1896 0) ++ [false,false]) ++ List.replicate 98 false) := by
    rw [List.append_assoc,←hrep]
    exact hbank
  have hresult0 : Holds out 5 (encode (0::List.replicate 1896 0) ++ [true,false,false]) := hresult'
  have hframe0 : ∀ q, 5+2+((List.replicate 0 true ++ (List.replicate 1896 0).flatMap
      (fun z => false :: List.replicate (z+1) true)).length : Int)<q → out q=t q := by
    intro q hq
    apply hright
    norm_num only [Nat.reduceMul,Nat.cast_ofNat,Int.reduceAdd,Int.reduceNeg,add_zero]
    exact hq
  have hbankfull : Holds out 5 ((encode (List.replicate 1897 0) ++ [true,false,false]) ++ List.replicate 98 false) := by
    have hh := positive_bank_padding t out 5 0 (List.replicate 1896 0) (List.replicate 98 false)
      hbankpad hresult0 hframe0
    exact hh
  have hnext := positive_short_dispatch (-3822) t out hprefix
    (by simpa using hleft3) (by simpa using hleft4) (by simpa using hleft5)
    (by simpa using hleft)
  have hnext' : silentSegment machine (cfg 83 (-3799) out) (cfg 93 (-3820) out) 31 := by
    simpa using hnext
  have hmid := segAdd machine _ _ _ _ j hseg hbody'
  have hall := segAdd machine _ _ _ _ 31 hmid hnext'
  exact ⟨m,n,k,j,out,hm,hn,hk,hj,hsmall,hunit,hhead1,hhead0,hl3,hl4,hl5,hray',
    by simpa using hmark,by simpa using hblank,hbankfull,by simpa using hcorr,by simpa using hstop,hall⟩

/-- Retain the earlier padded redispatch interface. -/
theorem blank_start_post_increment_redispatch_with_padding :
    ∃ (m n k j : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      Holds out (-3820) (zeroWord.take 22) ∧
      Holds out (-3820) (markerWindow (List.replicate 10 0 ++ [1])) ∧ out (-3821)=true ∧ out (-3822)=false ∧
      out (-3823)=false ∧ out (-3824)=false ∧ out (-3825)=false ∧
      out (-3798)=true ∧ out 4=false ∧
      Holds out 5 ((encode (List.replicate 1897 0) ++ [true,false,false]) ++ List.replicate 98 false) ∧
      (∀ q, -3798<q → q<3 → out q=false) ∧ out 3=true ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31) := by
  obtain ⟨m,n,k,j,out,hm,hn,hk,hj,hpre,hunit,h1,h2,h3,h4,h5,_hray,hmark,hdelim,hbank,hcorr,hstop,hseg⟩ :=
    blank_start_post_increment_redispatch_with_left_ray
  exact ⟨m,n,k,j,out,hm,hn,hk,hj,hpre,hunit,h1,h2,h3,h4,h5,hmark,hdelim,hbank,hcorr,hstop,hseg⟩

/-- Retain the earlier reachable redispatch interface. -/
theorem blank_start_post_increment_positive_redispatch :
    ∃ (m n k j : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧ 0<j ∧
      out (-3798)=true ∧ out 4=false ∧
      Holds out 5 (encode (List.replicate 1897 0) ++ [true,false,false]) ∧
      (∀ q, -3798<q → q<3 → out q=false) ∧ out 3=true ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+30492+7652+j+31) := by
  obtain ⟨m,n,k,j,out,hm,hn,hk,hj,_hp,_hunit,_h1,_h2,_h3,_h4,_h5,hmark,hblank,hbank,hcorr,hstop,hseg⟩ :=
    blank_start_post_increment_redispatch_with_padding
  have hb := holds_prefix_word out 5 (encode (List.replicate 1897 0) ++ [true,false,false])
    (List.replicate 98 false) hbank
  exact ⟨m,n,k,j,out,hm,hn,hk,hj,hmark,hblank,hb,hcorr,hstop,hseg⟩

#print axioms blank_start_post_increment_positive_redispatch
end Shared.Beeping.NPcoNP.Bootstrap284PostIncrementRedispatch
