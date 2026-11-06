import Shared.Beeping.NPcoNP.NativeFirstZeroOperation

/-! Connect the beep carry's cleared corridor to the literal zero-branch
scanner. This conditional finite segment is a building block for a full
physical refinement; it does not identify the next graph instruction. -/
namespace Shared.Beeping.NPcoNP.NativeFirstZeroCycle
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeBeepForwardControl
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeFirstZeroOperation
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- A supplied beep layout with a short one-run produces its own finite
terminating marker for the next scanner. The returned state-83 configuration
and full tape update are exact; the suffix after the separator is preserved. -/
theorem supplied_beep_zero_cycle_detail (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q≤h+6 → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsep : h+3<separator) (hsepzero : t separator=false) :
    ∃ (n : Nat) (mid : Int → Bool) (stop : Int), 1<n ∧
      h+6≤stop ∧ stop<separator ∧ t (stop+1)=false ∧ mid stop=true ∧
      Holds mid (h-4) [true,true,false,true,false,false] ∧
      (∀ q, q<h-4 → mid q=false) ∧
      (∀ q, h≤q → q<stop → mid q=false) ∧
      (∀ q, separator≤q →
        fillRange (setAt (h+2) mid) (h+5) stop q=t q) ∧
      physical.advance (cfg 99 h t) n=
        cfg 83 (stop-2) (fillRange (setAt (h+2) mid) (h+5) stop) ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  have hmark : t (h+3)=true := ones (h+3) (by omega) (by omega)
  obtain ⟨n,mid,hn,h2,hword,_hparse,hprefix,
      ⟨stop,hstop,hsep',hstopT,hstopNext,hstopMid,hclear⟩,hframe,ha,hw⟩ :=
    beep_returns_forward_decrement_bank_with_clear h (h+3) b separator t ht hm1 hm2 hm3 hm4 hp1
      hb right (by omega) hmark hsep hsepzero
  have hleft : ∀ q, q<h-4 → mid q=false := by
    intro q hq
    rw [hprefix q (by omega)]
    exact left q hq
  have h3 : mid (h-3)=true := by
    have hv := hword
    simp only [Holds] at hv
    have he : h-4+1=h-3 := by omega
    simpa only [he] using hv.2.1
  have h4 : mid (h-4)=true := by
    have hv := hword
    simp only [Holds] at hv
    exact hv.1
  have h1 : mid (h-1)=true := by
    have hv := hword
    simp only [Holds] at hv
    have he : h-4+1+1+1=h-1 := by omega
    simpa only [he] using hv.2.2.2.1
  have hstopge : h+3≤stop := by
    by_contra hn'
    have he : stop=h+1 ∨ stop=h+2 := by omega
    rcases he with he | he
    · rw [he,hp1] at hstopT; contradiction
    · rw [he,hp2] at hstopT; contradiction
  have hstopbig : h+6≤stop := by
    by_contra hn'
    have ho := ones (stop+1) (by omega) (by omega)
    rw [hstopNext] at ho
    contradiction
  let k := (stop-(h+5)).toNat
  have hkval : (k : Int)=stop-(h+5) := Int.toNat_of_nonneg (by omega)
  have hk : 0<k := by omega
  have he : h+5+(k : Int)=stop := by omega
  have hfirst : ∀ i : Nat, i<5 → mid (h+(i : Int))=false := by
    intro i hi
    apply hclear <;> omega
  have hzeros : ∀ i : Nat, i<k → mid (h+5+(i : Int))=false := by
    intro i hi
    apply hclear <;> omega
  have hmarker : mid (h+5+(k : Int))=true := by rw [he]; exact hstopMid
  obtain ⟨hfillFrame,hscan⟩ := zero_to83 h mid k hk hfirst hzeros hmarker
  have hscan' : silentSegment machine (cfg 166 h mid)
      (cfg 83 (stop-2) (fillRange (setAt (h+2) mid) (h+5) stop)) (k+7) := by
    simpa only [he] using hscan
  have hsel := selector_first_path h mid h2 h3 h4 hleft
  have hdispatch := dispatch_93_to166 h mid h3 h2 h1
  have hpre : silentSegment machine (cfg 83 (h-2) mid) (cfg 166 h mid) 34 :=
    segAdd machine _ _ _ 31 3 hsel hdispatch
  have hrest := segAdd machine _ _ _ 34 (k+7) hpre hscan'
  obtain ⟨ha',hw'⟩ := append_silent (cfg 99 h t) (cfg 83 (h-2) mid) _ n (34+(k+7)) ha hw hrest
  refine ⟨n+(34+(k+7)),mid,stop,by omega,hstopbig,hsep',hstopNext,hstopMid,hword,hleft,hclear,?_,ha',hw'⟩
  intro q hq
  have hv := hfillFrame q (by rw [he]; omega)
  rw [he] at hv
  rw [hv]
  exact hframe q hq

/-- Compatibility interface for the first zero cycle. -/
theorem supplied_beep_zero_cycle (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q≤h+6 → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsep : h+3<separator) (hsepzero : t separator=false) :
    ∃ (n : Nat) (mid : Int → Bool) (stop : Int), 1<n ∧
      h+6≤stop ∧ stop<separator ∧ mid stop=true ∧
      Holds mid (h-4) [true,true,false,true,false,false] ∧
      (∀ q, q<h-4 → mid q=false) ∧
      (∀ q, h≤q → q<stop → mid q=false) ∧
      (∀ q, separator≤q → fillRange (setAt (h+2) mid) (h+5) stop q=t q) ∧
      physical.advance (cfg 99 h t) n=
        cfg 83 (stop-2) (fillRange (setAt (h+2) mid) (h+5) stop) ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,mid,stop,hn,hs,hsep',_hz,hm,hw,hl,hc,hf,ha,he⟩ :=
    supplied_beep_zero_cycle_detail h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2 ones left
      hb right hsep hsepzero
  exact ⟨n,mid,stop,hn,hs,hsep',hm,hw,hl,hc,hf,ha,he⟩

#print axioms supplied_beep_zero_cycle_detail
#print axioms supplied_beep_zero_cycle
end Shared.Beeping.NPcoNP.NativeFirstZeroCycle
