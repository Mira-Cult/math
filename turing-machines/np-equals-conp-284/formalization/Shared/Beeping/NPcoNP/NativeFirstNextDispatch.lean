import Shared.Beeping.NPcoNP.NativeFirstNextPath

/-! Compose the initial flagged transition, zero-bank restoration, state-25
return, next carry, and literal dispatch of the next retained grammar path.
The theorem is conditional on the supplied physical first-event layout. -/
namespace Shared.Beeping.NPcoNP.NativeFirstNextDispatch
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeFirstZeroRestored
open Shared.Beeping.NPcoNP.NativeFirstReturn25
open Shared.Beeping.NPcoNP.NativeFirstNextPath
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- The supplied zero-bank first-event layout reaches the actual state-62
branch of the next complete producer path, retaining the entire bank suffix
and emitting exactly one beep. The complete path is retained graph row 2. -/
theorem supplied_beep_next_dispatch_full (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+7≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (tail : List Bool)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      Holds out (h-4) nextPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.4.decnz",10) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) ∧
      physical.advance (cfg 99 h t) n=cfg 62 (h+6) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,mid,hn,hword,hleft,hcontrol,hframe,hbank,ha,hw⟩ :=
    supplied_beep_zero_restored_full h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero tail bank
  have hsep : mid separator=false := by rw [hframe separator (le_refl _)]; exact hsepzero
  let r := (separator-(h+6)).toNat
  let ys := unaryBankPrefix r (List.replicate 5 0)
  have h25 := return25_to1 h separator mid tail hlong hword hcontrol hsep hbank
  change silentSegment machine (cfg 25 (separator+10) mid) (cfg 1 h mid) (ys.length+5) at h25
  obtain ⟨ha1,hw1⟩ := append_silent _ _ _ n (ys.length+5) ha hw h25
  let bound := max b separator
  have hright : ∀ q, bound≤q → mid q=false := by
    intro q hq
    rw [hframe q (le_trans (le_max_right _ _) hq)]
    exact right q (le_trans (le_max_left _ _) hq)
  obtain ⟨m,out,hm,hpath,hparse,hblank,hgap,hmarker,hframe2,hcarry⟩ :=
    carry_to_next_path_full h bound separator mid hlong hword hleft hcontrol hsep hright
  obtain ⟨ha2,hw2⟩ := append_silent _ _ _ (n+(ys.length+5)) m ha1 hw1 hcarry
  have hdispatch := dispatch_next_path h out hpath
  obtain ⟨ha3,hw3⟩ := append_silent _ _ _ (n+(ys.length+5)+m) 9 ha2 hw2 hdispatch
  have hfinal : ∀ q, separator≤q → out q=t q := by
    intro q hq
    rw [hframe2 q hq]
    exact hframe q hq
  have hbankFinal : Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) := by
    apply holds_transport t out _ _ bank
    intro q hq _
    exact (hfinal q (by omega)).symm
  exact ⟨n+(ys.length+5)+m+9,out,by omega,hpath,hparse,hblank,hgap,hmarker,hfinal,hbankFinal,ha3,hw3⟩

/-- Compatibility projection of the strengthened startup invariant. -/
theorem supplied_beep_next_dispatch (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+7≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (tail : List Bool)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      Holds out (h-4) nextPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.4.decnz",10) ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) ∧
      physical.advance (cfg 99 h t) n=cfg 62 (h+6) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,out,hn,hpath,hparse,_,_,_,hframe,hbank,ha,hw⟩ :=
    supplied_beep_next_dispatch_full h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero tail bank
  exact ⟨n,out,hn,hpath,hparse,hframe,hbank,ha,hw⟩

#print axioms supplied_beep_next_dispatch
end Shared.Beeping.NPcoNP.NativeFirstNextDispatch
