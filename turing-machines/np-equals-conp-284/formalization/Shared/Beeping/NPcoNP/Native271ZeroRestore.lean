import Shared.Beeping.NPcoNP.Native271BankScan
import Shared.Beeping.NPcoNP.Native271ZeroWindow

/-! Literal state-271 first-bank zero scan and restoration. -/
namespace Shared.Beeping.NPcoNP.Native271ZeroRestore
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Native271BankScan
open Shared.Beeping.NPcoNP.Native271ZeroWindow
open Shared.Beeping.NPcoNP.NativeZeroRestore
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- The first zero bank block is temporarily touched and restored in finite
silent time, with exact output tape and the complete bank suffix unchanged. -/
theorem zero_touch_restore_first (h separator : Int) (t : Int → Bool) (tail : List Bool)
    (hlong : h+7≤separator)
    (mark : t (h+2)=true) (z1 : t (h+3)=false) (z2 : t (h+4)=false)
    (ones : ∀ q, h+5≤q → q<separator → t q=true)
    (sep : t separator=false) (bank : Holds t (separator+1) (block 0 ++ tail)) :
    let k := (separator-(h+5)).toNat
    let touched := clearAt (separator+1) t
    let out := setAt (separator+1) (setAt (h+4) (clearAt (h+2) touched))
    (∀ q, separator≤q → out q=t q) ∧
    (∀ q, q<h+2 → out q=t q) ∧
    out (h+2)=false ∧ out (h+4)=true ∧
    silentSegment machine (cfg 271 (h+3) t) (cfg 25 separator out) (k+5+(2*k+9)) := by
  dsimp only
  let k := (separator-(h+5)).toNat
  let ys := List.replicate k true
  let touched := clearAt (separator+1) t
  let out := setAt (separator+1) (setAt (h+4) (clearAt (h+2) touched))
  have hk : (k : Int)=separator-(h+5) := Int.toNat_of_nonneg (by omega)
  have hc : ∀ i : Nat, i<k → t (h+3+2+(i : Int))=true := by
    intro i hi
    apply ones <;> omega
  have hd : t (h+3+2+(k : Int))=false := by
    have he : h+3+2+(k : Int)=separator := by omega
    simpa only [he] using sep
  have hb : Holds t (h+3+3+(k : Int)) (block 0 ++ tail) := by
    have he : h+3+3+(k : Int)=separator+1 := by omega
    simpa only [he] using bank
  obtain ⟨_frame,hscan⟩ := scan271_to262 (h+3) t k 0 tail z1
    (by simpa [Int.add_assoc] using z2) hc hd hb
  have hscan' : silentSegment machine (cfg 271 (h+3) t) (cfg 262 (separator-1) touched) (k+5) := by
    have hp : h+3+3+(k : Int)=separator+1 := by omega
    have he : separator+1-2=separator-1 := by omega
    simpa only [hp,he,touched] using hscan
  have htarget : Holds t (separator+1) (true::false::tail) := by
    simpa only [block_zero,List.cons_append,List.nil_append] using bank
  have htargetOne : t (separator+1)=true := htarget.1
  have htargetZero : t (separator+2)=false := by
    have he : separator+1+1=separator+2 := by omega
    simpa only [Holds,he] using htarget.2.1
  have htargetTouched : Holds touched (separator+1) [false,false] := by
    have he : separator+1+1=separator+2 := by omega
    simp [Holds,touched,clearAt,he,show separator+2≠separator+1 by omega,htargetZero]
  have hm : touched (h+2)=true := by simp [touched,clearAt,show h+2≠separator+1 by omega,mark]
  have hz1 : touched (h+3)=false := by simp [touched,clearAt,show h+3≠separator+1 by omega,z1]
  have hz2 : touched (h+4)=false := by simp [touched,clearAt,show h+4≠separator+1 by omega,z2]
  have ho : ∀ q, h+5≤q → q<separator → touched q=true := by
    intro q hq hq2
    simp [touched,clearAt,show q≠separator+1 by omega,ones q hq hq2]
  have hsep : touched separator=false := by simp [touched,clearAt,show separator≠separator+1 by omega,sep]
  obtain ⟨hys,hxs,hleft,hright,hpos⟩ := zero_windows_first h separator touched hlong hz1 hz2 ho hsep htargetTouched
  have hl : ys.reverse.length=ys.length := by simp
  have hp : separator+1=(h+2)+(ys.reverse.length : Int)+4 := by simpa only [hl] using hpos
  have hlft : downHolds touched (separator+1-2) (ys.reverse ++ [false,false]) := by
    have he : separator+1-2=separator-1 := by omega
    simpa only [he] using hleft
  have hrght : Holds touched (h+2+3) (ys ++ [false,false,false]) := by
    have he : h+2+3=h+5 := by omega
    simpa only [he] using hright
  obtain ⟨_hout,_hframe,hrestore⟩ := restore_zero touched (h+2) (separator+1)
    ys.reverse ys hxs hys hl hp hlft hm (by simpa [Int.add_assoc] using hz1)
    (by simpa [Int.add_assoc] using hz2) hrght
  have hrestore' : silentSegment machine (cfg 262 (separator-1) touched)
      (cfg 25 separator out) (2*k+9) := by
    have he1 : separator+1-2=separator-1 := by omega
    have he2 : separator+1-1=separator := by omega
    have he3 : h+2+2=h+4 := by omega
    simpa only [he1,he2,he3,out,ys,List.length_reverse,List.length_replicate] using hrestore
  have hall := segAdd machine _ _ _ (k+5) (2*k+9) hscan' hrestore'
  refine ⟨?_,?_,?_,?_,hall⟩
  · intro q hq
    by_cases he : q=separator+1
    · subst q; simp [out,setAt,htargetOne]
    · simp [out,touched,setAt,clearAt,he,show q≠h+4 by omega,show q≠h+2 by omega]
  · intro q hq
    simp [out,touched,setAt,clearAt,show q≠separator+1 by omega,
      show q≠h+4 by omega,show q≠h+2 by omega]
  · simp [out,touched,setAt,clearAt,show h+2≠separator+1 by omega,show h+2≠h+4 by omega]
  · simp [out,setAt,show h+4≠separator+1 by omega]

#print axioms zero_touch_restore_first
end Shared.Beeping.NPcoNP.Native271ZeroRestore
