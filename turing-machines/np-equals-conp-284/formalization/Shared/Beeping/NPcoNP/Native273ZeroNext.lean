import Shared.Beeping.NPcoNP.Native273ZeroFrame
import Shared.Beeping.NPcoNP.NativeBankReturnGeneric
import Shared.Beeping.NPcoNP.NativeFifthZeroCarryPath

/-! Zero bank operation through the next literal dispatch. The finite tape
layout and blank right tail are explicit. -/
namespace Shared.Beeping.NPcoNP.Native273ZeroNext
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.Native273ZeroRestore
open Shared.Beeping.NPcoNP.Native273ZeroFrame
open Shared.Beeping.NPcoNP.NativeBankReturnGeneric
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.NativeFifthZeroNextPath
open Shared.Beeping.NPcoNP.NativeFifthZeroCarryPath
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- For arbitrary ten-value prefixes and a zero target, the complete bank
restoration, return, carry, selector and dispatch terminate silently at state
64. The entire bank suffix and the next prepared path are retained. -/
theorem zero_to_next_dispatch_full (h b separator : Int) (t : Int → Bool)
    (values : List Nat) (tail : List Bool) (hlen : values.length=10)
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, b≤q → t q=false)
    (bank : Holds t (separator+1) (encode values ++ (block 0 ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      Holds out (h-4) zeroNextPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.5.decnz",12) ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode values ++ (block 0 ++ tail)) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+5<q → q<separator-1 → out q=false) ∧ out (separator-1)=true ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 64 (h+8) out) n := by
  let pos := separator+1+((encode values).length : Int)
  let k := (separator-((h+5)+5)).toNat
  let r := (separator-((h+5)+6)).toNat
  let ys := unaryBankPrefix r values
  let touched := clearAt pos t
  let mid := setAt pos (setAt ((h+5)+4) (clearAt ((h+5)+2) touched))
  have hpos : separator+1≤pos := by dsimp [pos]; omega
  have hzero := zero_touch_restore_273 (h+5) separator t values tail hlen
    (by omega) (by simpa [Int.add_assoc] using mark) (by simpa [Int.add_assoc] using z1)
    (by simpa [Int.add_assoc] using z2) (by intro q hq hq2; exact ones q (by omega) hq2) sep bank
  have hframe := zero_control_frame (h+5) separator t values tail hlen
    (by omega) (by simpa [Int.add_assoc] using mark) (by simpa [Int.add_assoc] using z1)
    (by simpa [Int.add_assoc] using z2) (by intro q hq hq2; exact ones q (by omega) hq2) sep bank
  have hp : Holds mid (h-4) fifthPath := by
    apply holds_transport t mid _ _ path
    intro q _ hq
    have hq' : q<h+7 := by simp [fifthPath] at hq; omega
    have hf : mid q=t q := hframe.2.2.2.2.2.1 q (by omega) (by omega) (by omega)
    exact hf.symm
  have hleft : ∀ q, q<h-4 → mid q=false := by
    intro q hq
    have hf : mid q=t q := hframe.2.2.2.2.2.1 q (by omega) (by omega) (by omega)
    rw [hf]
    exact left q hq
  have ht7 : mid ((h+5)+2)=false := hframe.1
  have ht8 : mid ((h+5)+3)=false := hframe.2.1
  have ht9 : mid ((h+5)+4)=true := hframe.2.2.1
  have h7 : mid (h+7)=false := by
    have he : h+5+2=h+7 := by omega
    simpa only [he] using ht7
  have h8 : mid (h+8)=false := by
    have he : h+5+3=h+8 := by omega
    simpa only [he] using ht8
  have h9 : mid (h+9)=true := by
    have he : h+5+4=h+9 := by omega
    simpa only [he] using ht9
  have h6 : mid (h+6)=false := by
    have hv := hp
    simp only [fifthPath,Holds] at hv
    obtain ⟨_,_,_,_,_,_,_,_,_,_,hp6,_⟩ := hv
    convert hp6 using 1 <;> congr 1 <;> omega
  have hcontrol : ∀ q, h+9≤q → q<separator → mid q=true := by
    intro q hq hq2
    by_cases he : q=h+9
    · simpa only [he] using h9
    · exact hframe.2.2.2.1 q (by omega) hq2
  have hsep : mid separator=false := hframe.2.2.2.2.1
  have hfinal : ∀ q, separator≤q → mid q=t q := hframe.2.2.2.2.2.2
  have hbank : Holds mid (separator+1) (encode values ++ (block 0 ++ tail)) := by
    apply holds_transport t mid _ _ bank
    intro q hq _
    exact (hfinal q (by omega)).symm
  let rr := (separator-((h+5)+6)).toNat
  let yy := unaryBankPrefix rr values
  have hreturn := return25_generic (h+5) separator mid values (block 0 ++ tail) (by omega)
    (by simpa [Int.add_assoc] using h6) (by simpa [Int.add_assoc] using h7)
    (by simpa [Int.add_assoc] using h8)
    (by intro q hq hq2; exact hcontrol q (by omega) hq2) hsep hbank
  have hreturn' : silentSegment machine (cfg 25 (pos-1) mid) (cfg 1 (h+5) mid) (yy.length+5) := by
    have he : separator+((encode values).length : Int)=pos-1 := by dsimp [pos]; omega
    simpa only [he,rr,yy] using hreturn
  let bound := max b separator
  have hright : ∀ q, bound≤q → mid q=false := by
    intro q hq
    rw [hfinal q (le_trans (le_max_right _ _) hq)]
    exact right q (le_trans (le_max_left _ _) hq)
  obtain ⟨m,out,hm,hpath,hparse,hleft',hgap,hmarker,hsuffix,hcarry⟩ :=
    carry_to_zero_next_path h bound separator mid hlong hp hleft h7 h8 hcontrol hsep hright
  have hframeOut : ∀ q, separator≤q → out q=t q := by
    intro q hq
    rw [hsuffix q hq]
    exact hfinal q hq
  have hbankOut : Holds out (separator+1) (encode values ++ (block 0 ++ tail)) := by
    apply holds_transport t out _ _ bank
    intro q hq _
    exact (hframeOut q (by omega)).symm
  have hstep := dispatch_zero_next_path h out hpath
  have hbody : silentSegment machine (cfg 273 (h+8) t) (cfg 25 (pos-1) mid)
      (k+(encode values).length+5+(2*ys.reverse.length+9)) := by
    have he : h+5+3=h+8 := by omega
    simpa only [he,k,r,ys,pos,touched,mid] using hzero.2.2.2.2
  have a := segAdd machine _ _ _ _ _ hbody hreturn'
  have bb := segAdd machine _ _ _ _ _ a hcarry
  have all := segAdd machine _ _ _ _ 11 bb hstep
  exact ⟨_,out,by omega,hpath,hparse,hframeOut,hbankOut,hleft',hgap,hmarker,all⟩

theorem zero_to_next_dispatch (h b separator : Int) (t : Int → Bool)
    (values : List Nat) (tail : List Bool) (hlen : values.length=10)
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, b≤q → t q=false)
    (bank : Holds t (separator+1) (encode values ++ (block 0 ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      Holds out (h-4) zeroNextPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.5.decnz",12) ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode values ++ (block 0 ++ tail)) ∧
      (∀ q, q<h-4 → out q=false) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 64 (h+8) out) n := by
  obtain ⟨n,out,hn,hpath,hparse,hframe,hbank,hleft,_,_,hseg⟩ :=
    zero_to_next_dispatch_full h b separator t values tail hlen hlong path left mark z1 z2 ones sep right bank
  exact ⟨n,out,hn,hpath,hparse,hframe,hbank,hleft,hseg⟩

#print axioms zero_to_next_dispatch_full
#print axioms zero_to_next_dispatch
end Shared.Beeping.NPcoNP.Native273ZeroNext
