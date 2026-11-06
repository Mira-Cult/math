import Shared.Beeping.NPcoNP.Native72Redispatch

/-! Conditional startup through the row-5 preparation and redispatch. -/
namespace Shared.Beeping.NPcoNP.NativeThirdPreparedRedispatch
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeSecondNextPath
open Shared.Beeping.NPcoNP.Native72Redispatch
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- From the supplied first-event layout, row-5 preparation and redispatch
reach state 271 with the bank suffix preserved and exactly one beep. -/
theorem supplied_beep_third_prepared_full (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+11≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (tail : List Bool)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      Holds out (h-4) thirdPath ∧ (∀ q, q<h-4 → out q=false) ∧
      out (h+6)=true ∧ out (h+7)=false ∧ out (h+8)=false ∧
      (∀ q, h+9≤q → q<separator → out q=true) ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) ∧
      physical.advance (cfg 99 h t) n=cfg 271 (h+7) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,mid,hn,hpath,_hparse,hleft,hgap,hmarker,hframe,_hbank,ha,hw⟩ :=
    supplied_beep_third_dispatch h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero tail bank
  let r := (separator-(h+11)).toNat
  have hr : (r : Int)=separator-(h+11) := Int.toNat_of_nonneg (by omega)
  have hg : ∀ q, h+4<q → q<h+10+(r : Int) → mid q=false := by
    intro q hq hq2
    apply hgap q hq
    omega
  have hm : mid (h+10+(r : Int))=true := by
    have he : h+10+(r : Int)=separator-1 := by omega
    simpa only [he] using hmarker
  let out := NativeHalfState10Exact.fillRange (NativeHalfState14Progress.setAt (h+6) mid)
    (h+9) (h+10+(r : Int))
  have hprep := prepare_and_redispatch h r mid hpath hleft hg hm
  have houtleft : ∀ q, q<h+6 → out q=mid q := by
    intro q hq
    have hn : ¬ (h+9≤q ∧ q<h+10+(r : Int)) := by omega
    simp [out,fillRange,setAt,hn,show q≠h+6 by omega]
  have hpathOut : Holds out (h-4) thirdPath := by
    apply holds_transport mid out _ _ hpath
    intro q _ hq
    have hq' : q<h+6 := by simp [thirdPath] at hq; omega
    exact (houtleft q hq').symm
  have hleftOut : ∀ q, q<h-4 → out q=false := by
    intro q hq
    rw [houtleft q (by omega)]
    exact hleft q hq
  have hout6 : out (h+6)=true := by simp [out,fillRange,setAt]
  have hout7 : out (h+7)=false := by
    have hmid : mid (h+7)=false := hg _ (by omega) (by omega)
    simp [out,fillRange,setAt,show h+7≠h+6 by omega,hmid]
  have hout8 : out (h+8)=false := by
    have hmid : mid (h+8)=false := hg _ (by omega) (by omega)
    simp [out,fillRange,setAt,show h+8≠h+6 by omega,hmid]
  have houtones : ∀ q, h+9≤q → q<separator → out q=true := by
    intro q hq hq2
    by_cases hq3 : q<h+10+(r : Int)
    · have hin : h+9≤q ∧ q<h+10+(r : Int) := ⟨hq,hq3⟩
      simp [out,fillRange,hin]
    · have he : q=separator-1 := by omega
      subst q
      have hn : ¬ (h+9≤separator-1 ∧ separator-1<h+10+(r : Int)) := by omega
      simp [out,fillRange,setAt,hn,show separator-1≠h+6 by omega,hmarker]
  have hframe2 : ∀ q, separator≤q → out q=mid q := by
    intro q hq
    apply hprep.1
    omega
  have hfinal : ∀ q, separator≤q → out q=t q := by
    intro q hq
    rw [hframe2 q hq]
    exact hframe q hq
  have hbankFinal : Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) := by
    apply holds_transport t out _ _ bank
    intro q hq _
    exact (hfinal q (by omega)).symm
  obtain ⟨ha2,hw2⟩ := append_silent _ _ _ n (2*r+45) ha hw hprep.2
  exact ⟨n+(2*r+45),out,by omega,hpathOut,hleftOut,hout6,hout7,hout8,houtones,hfinal,hbankFinal,ha2,hw2⟩

/-- Compatibility projection of the stronger prepared-layout contract. -/
theorem supplied_beep_third_prepared (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+11≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (tail : List Bool)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) ∧
      physical.advance (cfg 99 h t) n=cfg 271 (h+7) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,out,hn,_,_,_,_,_,_,hf,hb,ha,hw⟩ :=
    supplied_beep_third_prepared_full h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero tail bank
  exact ⟨n,out,hn,hf,hb,ha,hw⟩

#print axioms supplied_beep_third_prepared_full
#print axioms supplied_beep_third_prepared
end Shared.Beeping.NPcoNP.NativeThirdPreparedRedispatch
