import Shared.Beeping.NPcoNP.NativeFourthPreparedRedispatch
import Shared.Beeping.NPcoNP.NativeZeroRestoreGeneric

/-! Conditional physical startup through the row-7 second-bank zero operation.
This finite execution theorem does not establish blank-start reachability or
the unbounded graph-control invariant. -/
namespace Shared.Beeping.NPcoNP.NativeFourthZeroRestored
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeThirdNextPath
open Shared.Beeping.NPcoNP.NativeFourthPreparedRedispatch
open Shared.Beeping.NPcoNP.Native279BankScan
open Shared.Beeping.NPcoNP.NativeZeroRestoreGeneric
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Under the supplied first-event layout, the second-bank zero operation finishes,
with exactly one beep, the complete bank suffix restored, and the row-7
control path retained. -/
theorem supplied_beep_fourth_zero_restored_full (h b separator : Int) (t : Int → Bool)
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
      Holds out (h-4) fourthPath ∧ (∀ q, q<h-4 → out q=false) ∧
      out (h+5)=false ∧ out (h+6)=false ∧ out (h+7)=false ∧ out (h+8)=true ∧
      (∀ q, h+8≤q → q<separator → out q=true) ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) ∧
      physical.advance (cfg 99 h t) n=cfg 25 (separator+2) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,mid,hn,hpath,hleft,hmark,hz1,hz2,hones,hframe,hbank,ha,hw⟩ :=
    supplied_beep_fourth_prepared_full h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero tail bank
  have hsep : mid separator=false := by rw [hframe separator (le_refl _)]; exact hsepzero
  have hmark' : mid ((h+4)+2)=true := by simpa [Int.add_assoc] using hmark
  have hz1' : mid ((h+4)+3)=false := by simpa [Int.add_assoc] using hz1
  have hz2' : mid ((h+4)+4)=false := by simpa [Int.add_assoc] using hz2
  have hones' : ∀ q, (h+4)+5≤q → q<separator → mid q=true := by
    intro q hq hq2
    exact hones q (by omega) hq2
  have hbankFirst : Holds mid (separator+1)
      (encode [0] ++ (block 0 ++ (encode (List.replicate 3 0) ++ (block 0 ++ tail)))) := by
    simpa [List.replicate_succ,encode,List.append_assoc] using hbank
  have chain : Chain 1 9 42 := .cons .r9 (.refl 42)
  have hzero := zero_touch_restore_generic RightRow.r275 RightRow.r271 RightRow.r270 chain
    (h+4) separator mid [0] (encode (List.replicate 3 0) ++ (block 0 ++ tail))
    (by decide) (by omega) hmark' hz1' hz2' hones' hsep hbankFirst
  have hlen : (encode [0]).length=2 := by decide
  have hpos : separator+1+((encode [0]).length : Int)=separator+3 := by rw [hlen]; omega
  simp only [hpos] at hzero
  let k := (separator-((h+4)+5)).toNat
  let r := (separator-((h+4)+6)).toNat
  let ys := unaryBankPrefix r [0]
  let out := setAt (separator+3) (setAt ((h+4)+4) (clearAt ((h+4)+2) (clearAt (separator+3) mid)))
  have hfinal : ∀ q, separator≤q → out q=t q := by
    intro q hq
    have hf : out q=mid q := hzero.1 q hq
    rw [hf]
    exact hframe q hq
  have hpathOut : Holds out (h-4) fourthPath := by
    apply holds_transport mid out _ _ hpath
    intro q _ hq
    have hq' : q<(h+4)+2 := by simp [fourthPath] at hq; omega
    exact (hzero.2.1 q hq').symm
  have hleftOut : ∀ q, q<h-4 → out q=false := by
    intro q hq
    have hf : out q=mid q := hzero.2.1 q (by omega)
    rw [hf]
    exact hleft q hq
  have hbankOut : Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) := by
    apply holds_transport t out _ _ bank
    intro q hq _
    exact (hfinal q (by omega)).symm
  have hseg : silentSegment machine (cfg 275 (h+7) mid) (cfg 25 (separator+2) out)
      (k+7+(2*ys.reverse.length+9)) := by
    have he : h+4+3=h+7 := by omega
    have hp : separator+3-1=separator+2 := by omega
    have ht : k+2+5=k+7 := by omega
    simpa only [he,hlen,hp,ht,k,r,ys,out] using hzero.2.2.2.2
  obtain ⟨ha2,hw2⟩ := append_silent _ _ _ n (k+7+(2*ys.reverse.length+9)) ha hw hseg
  have hm : out (h+6)=false := by
    have he : h+4+2=h+6 := by omega
    have hh : out (h+4+2)=false := hzero.2.2.1
    simpa only [he] using hh
  have hr : out (h+8)=true := by
    have he : h+4+4=h+8 := by omega
    have hh : out (h+4+4)=true := hzero.2.2.2.1
    simpa only [he] using hh
  have h5 : out (h+5)=false := by
    have hv := hpathOut
    simp only [fourthPath,Holds] at hv
    obtain ⟨_,_,_,_,_,_,_,_,_,hp5,_⟩ := hv
    convert hp5 using 1 <;> congr 1 <;> omega
  have h7 : out (h+7)=false := by
    simp [out,setAt,clearAt,show h+7≠separator+3 by omega,
      show h+7≠h+4+4 by omega,show h+7≠h+4+2 by omega,hz1]
  have hcontrol : ∀ q, h+8≤q → q<separator → out q=true := by
    intro q hq hq2
    by_cases he : q=h+8
    · simpa only [he] using hr
    · have hq9 : h+9≤q := by omega
      have ho := hones q hq9 hq2
      simp [out,setAt,clearAt,show q≠separator+3 by omega,
        show q≠h+4+4 by omega,show q≠h+4+2 by omega,ho]
  exact ⟨n+(k+7+(2*ys.reverse.length+9)),out,by omega,hpathOut,hleftOut,h5,hm,h7,hr,hcontrol,hfinal,hbankOut,ha2,hw2⟩

/-- The prior restoration interface is retained as a projection. -/
theorem supplied_beep_fourth_zero_restored (h b separator : Int) (t : Int → Bool)
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
      Holds out (h-4) fourthPath ∧ (∀ q, q<h-4 → out q=false) ∧
      out (h+6)=false ∧ out (h+8)=true ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) ∧
      physical.advance (cfg 99 h t) n=cfg 25 (separator+2) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,out,hn,hp,hl,_,h6,_,h8,_,hf,hb,ha,hw⟩ :=
    supplied_beep_fourth_zero_restored_full h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero tail bank
  exact ⟨n,out,hn,hp,hl,h6,h8,hf,hb,ha,hw⟩

#print axioms supplied_beep_fourth_zero_restored_full
#print axioms supplied_beep_fourth_zero_restored
end Shared.Beeping.NPcoNP.NativeFourthZeroRestored
