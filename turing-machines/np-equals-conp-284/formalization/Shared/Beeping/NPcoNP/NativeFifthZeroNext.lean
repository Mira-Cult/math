import Shared.Beeping.NPcoNP.Native273ZeroNext
import Shared.Beeping.NPcoNP.Native54Cycle

/-! Conditional initial event through the zero row-8 operation and next
literal dispatch. This does not establish blank-start reachability. -/
namespace Shared.Beeping.NPcoNP.NativeFifthZeroNext
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.Native54Cycle
open Shared.Beeping.NPcoNP.Native273ZeroNext
open Shared.Beeping.NPcoNP.NativeFifthZeroNextPath
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The supplied first-event execution, zero eleventh-block operation and
next literal dispatch form a finite segment with exactly one event. -/
theorem supplied_beep_zero_next_dispatch_full (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+12≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (xs : List Nat) (hxs : xs.length=4)
    (tail : List Bool)
    (bank : Holds t (separator+1)
      (encode (List.replicate 6 0 ++ xs) ++ (block 0 ++ tail))) :
    let values := List.replicate 6 0 ++ xs
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      Holds out (h-4) zeroNextPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.5.decnz",12) ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode values ++ (block 0 ++ tail)) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+5<q → q<separator-1 → out q=false) ∧ out (separator-1)=true ∧
      physical.advance (cfg 99 h t) n=cfg 64 (h+8) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  dsimp only
  let values := List.replicate 6 0 ++ xs
  let rest := encode xs ++ (block 0 ++ tail)
  have hbankFirst : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ rest)) := by
    have he : values = List.replicate 5 0 ++ (0::xs) := by simp [values,List.replicate_succ]
    have hh := bank
    change Holds t (separator+1) (encode values ++ (block 0 ++ tail)) at hh
    rw [he,encode_append] at hh
    simpa [rest,encode,List.append_assoc] using hh
  obtain ⟨n,mid,hn,hpath,hleft,hmark,hz1,hz2,hones,hframe,_hbank,ha,hw⟩ :=
    supplied_beep_fifth_prepared h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero rest hbankFirst
  have hsep : mid separator=false := by rw [hframe separator (le_refl _)]; exact hsepzero
  have hbankMid : Holds mid (separator+1) (encode values ++ (block 0 ++ tail)) := by
    apply holds_transport t mid _ _ bank
    intro q hq _
    exact (hframe q (by omega)).symm
  have hlen : values.length=10 := by simp [values,hxs]
  let bound := max b separator
  have hright : ∀ q, bound≤q → mid q=false := by
    intro q hq
    rw [hframe q (le_trans (le_max_right _ _) hq)]
    exact right q (le_trans (le_max_left _ _) hq)
  obtain ⟨m,out,hm,hnext,hparse,hsuffix,hbankOut,hleftOut,hgap,hmarker,hseg⟩ :=
    zero_to_next_dispatch_full h bound separator mid values tail hlen hlong hpath hleft
      hmark hz1 hz2 hones hsep hright hbankMid
  obtain ⟨ha2,hw2⟩ := append_silent _ _ _ n m ha hw hseg
  have hfinal : ∀ q, separator≤q → out q=t q := by
    intro q hq
    rw [hsuffix q hq]
    exact hframe q hq
  exact ⟨n+m,out,by omega,hnext,hparse,hfinal,hbankOut,hleftOut,hgap,hmarker,ha2,hw2⟩

/-- Compatibility interface retaining the original finite-prefix result. -/
theorem supplied_beep_zero_next_dispatch (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+12≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (xs : List Nat) (hxs : xs.length=4)
    (tail : List Bool)
    (bank : Holds t (separator+1)
      (encode (List.replicate 6 0 ++ xs) ++ (block 0 ++ tail))) :
    let values := List.replicate 6 0 ++ xs
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      Holds out (h-4) zeroNextPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.5.decnz",12) ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode values ++ (block 0 ++ tail)) ∧
      (∀ q, q<h-4 → out q=false) ∧
      physical.advance (cfg 99 h t) n=cfg 64 (h+8) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,out,hn,hpath,hparse,hframe,hbank,hleft,_,_,ha,hw⟩ :=
    supplied_beep_zero_next_dispatch_full h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero xs hxs tail bank
  exact ⟨n,out,hn,hpath,hparse,hframe,hbank,hleft,ha,hw⟩

#print axioms supplied_beep_zero_next_dispatch_full
#print axioms supplied_beep_zero_next_dispatch
end Shared.Beeping.NPcoNP.NativeFifthZeroNext
