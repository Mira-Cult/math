import Shared.Beeping.NPcoNP.Native279BankScan
import Shared.Beeping.NPcoNP.NativeZeroRestoreWindow

/-! Literal state-279 zero-bank scan and restoration. This reusable finite
segment is conditional on its supplied tape layout; it asserts no reachability
or unbounded graph simulation. -/
namespace Shared.Beeping.NPcoNP.Native279ZeroRestore
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Native279BankScan
open Shared.Beeping.NPcoNP.NativeZeroRestore
open Shared.Beeping.NPcoNP.NativeZeroRestoreWindow
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Starting with a marked control bit, two zeros, a filled control run,
separator and six zero-valued bank blocks, the physical machine completes the
zero branch silently, restoring the bank. The output tape and finite duration
are explicit; all cells at or beyond the separator are preserved. -/
theorem zero_touch_restore (h separator : Int) (t : Int → Bool) (tail : List Bool)
    (hlong : h+7≤separator)
    (mark : t (h+2)=true) (z1 : t (h+3)=false) (z2 : t (h+4)=false)
    (ones : ∀ q, h+5≤q → q<separator → t q=true)
    (sep : t separator=false)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    let k := (separator-(h+5)).toNat
    let r := (separator-(h+6)).toNat
    let ys := unaryBankPrefix r (List.replicate 5 0)
    let touched := clearAt (separator+11) t
    let out := setAt (separator+11) (setAt (h+4) (clearAt (h+2) touched))
    (∀ q, separator≤q → out q=t q) ∧
    (∀ q, q<h+2 → out q=t q) ∧
    out (h+2)=false ∧ out (h+4)=true ∧
    silentSegment machine (cfg 279 (h+3) t) (cfg 25 (separator+10) out)
      (k+15+(2*ys.reverse.length+9)) := by
  dsimp only
  let k := (separator-(h+5)).toNat
  let r := (separator-(h+6)).toNat
  let ys := unaryBankPrefix r (List.replicate 5 0)
  let touched := clearAt (separator+11) t
  let out := setAt (separator+11) (setAt (h+4) (clearAt (h+2) touched))
  have hk : (k : Int)=separator-(h+5) := Int.toNat_of_nonneg (by omega)
  have hlen : (encode (List.replicate 5 0)).length=10 := by decide
  have hc : ∀ i : Nat, i<k → t (h+3+2+(i : Int))=true := by
    intro i hi
    apply ones <;> omega
  have hd : t (h+3+2+(k : Int))=false := by
    have he : h+3+2+(k : Int)=separator := by omega
    simpa only [he] using sep
  have hb : Holds t (h+3+3+(k : Int))
      (encode (List.replicate 5 0) ++ (block 0 ++ tail)) := by
    have he : h+3+3+(k : Int)=separator+1 := by omega
    simpa only [he] using bank
  obtain ⟨_frame,hscan⟩ := scan279_to262 (h+3) t k (List.replicate 5 0) 0 tail
    (by decide) z1 (by simpa [Int.add_assoc] using z2) hc hd hb
  have hscan' : silentSegment machine (cfg 279 (h+3) t) (cfg 262 (separator+9) touched) (k+15) := by
    have hp : h+3+3+(k : Int)+(10 : Int)=separator+11 := by omega
    have he : separator+11-2=separator+9 := by omega
    have ht : k+10+5=k+15 := by omega
    simpa only [hlen,Nat.cast_ofNat,hp,he,ht,touched] using hscan
  have hpref : Holds t (separator+1) (encode (List.replicate 5 0)) :=
    holds_prefix_word t (separator+1) _ (block 0 ++ tail) bank
  have hpref' : Holds touched (separator+1) (encode (List.replicate 5 0)) := by
    apply holds_transport t touched _ _ hpref
    intro q hq hq2
    have hq3 : q<separator+11 := by rw [hlen] at hq2; omega
    simp [touched,clearAt,show q≠separator+11 by omega]
  have htarget := holds_append_tail t (separator+1) (encode (List.replicate 5 0)) (block 0 ++ tail) bank
  have htarget' : Holds t (separator+11) (true::false::tail) := by
    have he : separator+1+((encode (List.replicate 5 0)).length : Int)=separator+11 := by rw [hlen]; omega
    simpa only [he,block_zero,List.cons_append,List.nil_append] using htarget
  have htargetOne : t (separator+11)=true := htarget'.1
  have htargetZero : t (separator+12)=false := by
    have he : separator+11+1=separator+12 := by omega
    simpa only [Holds,he] using htarget'.2.1
  have htargetTouched : Holds touched (separator+11) [false,false] := by
    have he : separator+11+1=separator+12 := by omega
    simp [Holds,touched,clearAt,he,show separator+12≠separator+11 by omega,htargetZero]
  have hbank := holds_append_intro touched (separator+1) (encode (List.replicate 5 0))
    [false,false] hpref' (by
      have he : separator+1+((encode (List.replicate 5 0)).length : Int)=separator+11 := by rw [hlen]; omega
      simpa only [he] using htargetTouched)
  have hm : touched (h+2)=true := by simp [touched,clearAt,show h+2≠separator+11 by omega,mark]
  have hz1 : touched (h+3)=false := by simp [touched,clearAt,show h+3≠separator+11 by omega,z1]
  have hz2 : touched (h+4)=false := by simp [touched,clearAt,show h+4≠separator+11 by omega,z2]
  have ho : ∀ q, h+5≤q → q<separator → touched q=true := by
    intro q hq hq2
    simp [touched,clearAt,show q≠separator+11 by omega,ones q hq hq2]
  have hsep : touched separator=false := by simp [touched,clearAt,show separator≠separator+11 by omega,sep]
  obtain ⟨hys,hxs,hleft,hright,hpos⟩ := zero_windows h separator touched hlong hz1 hz2 ho hsep hbank
  have hl : ys.reverse.length=ys.length := by simp
  have hp : separator+11=(h+2)+(ys.reverse.length : Int)+4 := by simpa only [hl] using hpos
  have hlft : downHolds touched (separator+11-2) (ys.reverse ++ [false,false]) := by
    have he : separator+11-2=separator+9 := by omega
    simpa only [he] using hleft
  have hrght : Holds touched (h+2+3) (ys ++ [false,false,false]) := by
    have he : h+2+3=h+5 := by omega
    simpa only [he] using hright
  obtain ⟨_hout,hframe,hrestore⟩ := restore_zero touched (h+2) (separator+11)
    ys.reverse ys hxs hys hl hp hlft hm (by simpa [Int.add_assoc] using hz1)
    (by simpa [Int.add_assoc] using hz2) hrght
  have hrestore' : silentSegment machine (cfg 262 (separator+9) touched)
      (cfg 25 (separator+10) out) (2*ys.reverse.length+9) := by
    have he1 : separator+11-2=separator+9 := by omega
    have he2 : separator+11-1=separator+10 := by omega
    have he3 : h+2+2=h+4 := by omega
    simpa only [he1,he2,he3,out] using hrestore
  have hall := segAdd machine _ _ _ (k+15) (2*ys.reverse.length+9) hscan' hrestore'
  refine ⟨?_,?_,?_,?_,hall⟩
  · intro q hq
    by_cases he : q=separator+11
    · subst q; simp [out,setAt,htargetOne]
    · simp [out,touched,setAt,clearAt,he,show q≠h+4 by omega,show q≠h+2 by omega]
  · intro q hq
    simp [out,touched,setAt,clearAt,show q≠separator+11 by omega,
      show q≠h+4 by omega,show q≠h+2 by omega]
  · simp [out,touched,setAt,clearAt,show h+2≠separator+11 by omega,show h+2≠h+4 by omega]
  · simp [out,setAt,show h+4≠separator+11 by omega]

#print axioms zero_touch_restore
end Shared.Beeping.NPcoNP.Native279ZeroRestore
