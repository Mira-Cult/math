import Shared.Beeping.NPcoNP.Native280BankScan
import Shared.Beeping.NPcoNP.NativeZeroWindowGeneric

/-! Finite zero-bank operation for the literal state-280 six-block scanner. -/
namespace Shared.Beeping.NPcoNP.Native280ZeroRestore
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
open Shared.Beeping.NPcoNP.Native280BankScan
open Shared.Beeping.NPcoNP.NativeZeroRestore
open Shared.Beeping.NPcoNP.NativeZeroWindowGeneric
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- For any six encoded bank values, the following zero target is touched
and restored in finite silent time. No graph-register correspondence is assumed. -/
theorem zero_touch_restore_280 (h separator : Int) (t : Int → Bool)
    (values : List Nat) (tail : List Bool) (hlen : values.length=6)
    (hlong : h+6≤separator)
    (mark : t (h+2)=true) (z1 : t (h+3)=false) (z2 : t (h+4)=false)
    (ones : ∀ q, h+5≤q → q<separator → t q=true)
    (sep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ (block 0 ++ tail))) :
    let k := (separator-(h+5)).toNat
    let r := (separator-(h+6)).toNat
    let ys := unaryBankPrefix r values
    let pos := separator+1+((encode values).length : Int)
    let touched := clearAt pos t
    let out := setAt pos (setAt (h+4) (clearAt (h+2) touched))
    (∀ q, separator≤q → out q=t q) ∧
    (∀ q, q<h+2 → out q=t q) ∧ out (h+2)=false ∧ out (h+4)=true ∧
    silentSegment machine (cfg 280 (h+3) t) (cfg 25 (pos-1) out)
      (k+(encode values).length+5+(2*ys.reverse.length+9)) := by
  dsimp only
  let k := (separator-(h+5)).toNat
  let r := (separator-(h+6)).toNat
  let ys := unaryBankPrefix r values
  let pos := separator+1+((encode values).length : Int)
  let touched := clearAt pos t
  let out := setAt pos (setAt (h+4) (clearAt (h+2) touched))
  have hk : (k : Int)=separator-(h+5) := Int.toNat_of_nonneg (by omega)
  have hpos : separator+1≤pos := by dsimp [pos]; omega
  have hc : ∀ i : Nat, i<k → t (h+3+2+(i : Int))=true := by
    intro i hi
    apply ones <;> omega
  have hd : t (h+3+2+(k : Int))=false := by
    have he : h+3+2+(k : Int)=separator := by omega
    simpa only [he] using sep
  have hb : Holds t (h+3+3+(k : Int)) (encode values ++ (block 0 ++ tail)) := by
    have he : h+3+3+(k : Int)=separator+1 := by omega
    simpa only [he] using bank
  have hscan' : silentSegment machine (cfg 280 (h+3) t) (cfg 262 (pos-2) touched)
      (k+(encode values).length+5) := by
    obtain ⟨_frame,hscan⟩ := Native280BankScan.scan_to262 (h-6) separator t values 0 tail
      hlen (by omega) (by simpa only [show h-6+9=h+3 by omega] using z1)
      (by simpa only [show h-6+10=h+4 by omega] using z2)
      (by intro q hq hq'; exact ones q (by omega) hq') sep bank
    have he1 : h-6+9=h+3 := by omega
    have he2 : (separator-(h-6+11)).toNat=k := by dsimp [k]; congr 1 <;> omega
    simpa only [he1,he2,pos,touched] using hscan
  have hpref : Holds t (separator+1) (encode values) :=
    holds_prefix_word t (separator+1) _ (block 0 ++ tail) bank
  have hpref' : Holds touched (separator+1) (encode values) := by
    apply holds_transport t touched _ _ hpref
    intro q hq hq2
    have hq3 : q<pos := by dsimp [pos]; omega
    simp [touched,clearAt,show q≠pos by omega]
  have htarget := holds_append_tail t (separator+1) (encode values) (block 0 ++ tail) bank
  have htarget' : Holds t pos (true::false::tail) := by
    simpa only [pos,block_zero,List.cons_append,List.nil_append] using htarget
  have htargetOne : t pos=true := htarget'.1
  have htargetZero : t (pos+1)=false := htarget'.2.1
  have htargetTouched : Holds touched pos [false,false] := by
    simp [Holds,touched,clearAt,show pos+1≠pos by omega,htargetZero]
  have hbank := holds_append_intro touched (separator+1) (encode values) [false,false] hpref' (by
    simpa only [pos] using htargetTouched)
  have hm : touched (h+2)=true := by simp [touched,clearAt,show h+2≠pos by omega,mark]
  have hz1 : touched (h+3)=false := by simp [touched,clearAt,show h+3≠pos by omega,z1]
  have hz2 : touched (h+4)=false := by simp [touched,clearAt,show h+4≠pos by omega,z2]
  have ho : ∀ q, h+5≤q → q<separator → touched q=true := by
    intro q hq hq2
    simp [touched,clearAt,show q≠pos by omega,ones q hq hq2]
  have hsep : touched separator=false := by simp [touched,clearAt,show separator≠pos by omega,sep]
  obtain ⟨hys,hxs,hleft,hright,hposition⟩ := zero_windows_generic_min_gap h separator touched values hlong hz1 hz2 ho hsep hbank
  have hl : ys.reverse.length=ys.length := by simp
  have hp : pos=(h+2)+(ys.reverse.length : Int)+4 := by simpa only [hl,pos] using hposition
  have hrght : Holds touched (h+2+3) (ys ++ [false,false,false]) := by
    have he : h+2+3=h+5 := by omega
    simpa only [he] using hright
  obtain ⟨_hout,_hframe,hrestore⟩ := restore_zero touched (h+2) pos
    ys.reverse ys hxs hys hl hp hleft hm (by simpa [Int.add_assoc] using hz1)
    (by simpa [Int.add_assoc] using hz2) hrght
  have hrestore' : silentSegment machine (cfg 262 (pos-2) touched)
      (cfg 25 (pos-1) out) (2*ys.reverse.length+9) := by
    have he : h+2+2=h+4 := by omega
    simpa only [he,out] using hrestore
  have hall := segAdd machine _ _ _ (k+(encode values).length+5) (2*ys.reverse.length+9) hscan' hrestore'
  change (∀ q, separator≤q → out q=t q) ∧
    (∀ q, q<h+2 → out q=t q) ∧ out (h+2)=false ∧ out (h+4)=true ∧
    silentSegment machine (cfg 280 (h+3) t) (cfg 25 (pos-1) out)
      (k+(encode values).length+5+(2*ys.reverse.length+9))
  refine ⟨?_,?_,?_,?_,hall⟩
  · intro q hq
    by_cases he : q=pos
    · subst q; simp [out,setAt,htargetOne]
    · simp [out,touched,setAt,clearAt,he,show q≠h+4 by omega,show q≠h+2 by omega]
  · intro q hq
    simp [out,touched,setAt,clearAt,show q≠pos by omega,
      show q≠h+4 by omega,show q≠h+2 by omega]
  · simp [out,touched,setAt,clearAt,show h+2≠pos by omega,show h+2≠h+4 by omega]
  · simp [out,setAt,show h+4≠pos by omega]

#print axioms zero_touch_restore_280
end Shared.Beeping.NPcoNP.Native280ZeroRestore
