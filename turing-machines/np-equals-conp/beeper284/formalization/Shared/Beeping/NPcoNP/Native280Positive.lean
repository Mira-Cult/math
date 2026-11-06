import Shared.Beeping.NPcoNP.Native280BankScan
import Shared.Beeping.NPcoNP.NativeOneBlankWindow
import Shared.Beeping.NPcoNP.NativeBankRoundtrip
import Shared.Beeping.NPcoNP.NativeManyBankResult

/-! The state-280 six-block scanner followed by the positive-target branch.
All input windows and the two final blanks are explicit; this is not a
blank-start or graph-refinement theorem. -/
namespace Shared.Beeping.NPcoNP.Native280Positive
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
open Shared.Beeping.NPcoNP.Native280BankScan
open Shared.Beeping.NPcoNP.NativeOneBlankWindow
open Shared.Beeping.NPcoNP.NativeBankRoundtrip
open Shared.Beeping.NPcoNP.NativeManyShift
open Shared.Beeping.NPcoNP.NativeManyBankResult
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- A positive target after six arbitrary encoded values is decremented, and
a zero reserve is appended. The exact finite silent duration, physical head,
and complete frame outside the changed control and bank intervals are stated. -/
theorem positive_touch_shift_280 (h separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (vs : List Nat) (hlen : values.length=6)
    (hlong : h+6≤separator)
    (mark : t (h+2)=true) (z1 : t (h+3)=false) (z2 : t (h+4)=false)
    (ones : ∀ q, h+5≤q → q<separator → t q=true)
    (sep : t separator=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::vs) ++ [false,false]))) :
    let k := (separator-(h+5)).toNat
    let r := (separator-(h+6)).toNat
    let ys := unaryBankPrefix r values
    let pos := separator+1+((encode values).length : Int)
    let touched := clearAt pos t
    let u := setAt (h+4) (clearAt (h+2) touched)
    let original := setAt pos u
    let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    let f := pos+2+(suffix.length : Int)
    let out := spec original f (suffix.length+2)
    Holds out pos (encode (v::vs) ++ [true,false,false]) ∧
    (∀ q, q<h+2 → out q=t q) ∧
    (∀ q, separator≤q → (q<pos ∨ f<q) → out q=t q) ∧
    silentSegment machine (cfg 280 (h+3) t) (cfg 23 (pos-2) out)
      (k+(encode values).length+5+(2*ys.reverse.length+7)+(2*suffix.length+7)) := by
  dsimp only
  let k := (separator-(h+5)).toNat
  let r := (separator-(h+6)).toNat
  let ys := unaryBankPrefix r values
  let pos := separator+1+((encode values).length : Int)
  let touched := clearAt pos t
  let u := setAt (h+4) (clearAt (h+2) touched)
  let original := setAt pos u
  let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  let f := pos+2+(suffix.length : Int)
  let out := spec original f (suffix.length+2)
  have hk : (k : Int)=separator-(h+5) := Int.toNat_of_nonneg (by omega)
  have hpos : separator+1≤pos := by dsimp [pos]; omega
  have hc : ∀ i : Nat, i<k → t (h+3+2+(i : Int))=true := by
    intro i hi
    apply ones <;> omega
  have hd : t (h+3+2+(k : Int))=false := by
    have he : h+3+2+(k : Int)=separator := by omega
    simpa only [he] using sep
  have hb : Holds t (h+3+3+(k : Int))
      (encode values ++ (block (v+1) ++ (encode vs ++ [false,false]))) := by
    have he : h+3+3+(k : Int)=separator+1 := by omega
    simpa only [he,encode,List.append_assoc] using bank
  have hscan : silentSegment machine (cfg 280 (h+3) t) (cfg 262 (pos-2) touched)
      (k+(encode values).length+5) := by
    obtain ⟨_frame,hs⟩ := Native280BankScan.scan_to262 (h-6) separator t values (v+1)
      (encode vs ++ [false,false]) hlen (by omega)
      (by simpa only [show h-6+9=h+3 by omega] using z1)
      (by simpa only [show h-6+10=h+4 by omega] using z2)
      (by intro q hq hq'; exact ones q (by omega) hq') sep (by
        simpa [encode,List.append_assoc] using bank)
    have he1 : h-6+9=h+3 := by omega
    have he2 : (separator-(h-6+11)).toNat=k := by dsimp [k]; congr 1 <;> omega
    simpa only [he1,he2,pos,touched] using hs
  have hpref : Holds t (separator+1) (encode values) :=
    holds_prefix_word t (separator+1) _ (encode ((v+1)::vs) ++ [false,false]) bank
  have hpref' : Holds touched (separator+1) (encode values) := by
    apply holds_transport t touched _ _ hpref
    intro q hq hq2
    have hq3 : q<pos := by dsimp [pos]; omega
    simp [touched,clearAt,show q≠pos by omega]
  have htarget := holds_append_tail t (separator+1) (encode values)
    (encode ((v+1)::vs) ++ [false,false]) bank
  have htarget' : Holds t pos (encode ((v+1)::vs) ++ [false,false]) := by simpa only [pos] using htarget
  have htargetOne : t pos=true := by
    simpa [encode,block,List.replicate_succ,Holds] using htarget'.1
  have htargetTouched : Holds touched pos [false] := by simp [Holds,touched,clearAt]
  have hbank : Holds touched (separator+1) (encode values ++ [false]) := by
    apply holds_append_intro touched (separator+1) (encode values) [false] hpref'
    simpa only [pos] using htargetTouched
  have hm : touched (h+2)=true := by simp [touched,clearAt,show h+2≠pos by omega,mark]
  have hz1 : touched (h+3)=false := by simp [touched,clearAt,show h+3≠pos by omega,z1]
  have hz2 : touched (h+4)=false := by simp [touched,clearAt,show h+4≠pos by omega,z2]
  have ho : ∀ q, h+5≤q → q<separator → touched q=true := by
    intro q hq hq2
    simp [touched,clearAt,show q≠pos by omega,ones q hq hq2]
  have hsep : touched separator=false := by simp [touched,clearAt,show separator≠pos by omega,sep]
  obtain ⟨hys,hxs,hleft,hright,hposition⟩ := one_blank_windows_min_gap h separator touched values hlong hz1 hz2 ho hsep hbank
  have hl : ys.reverse.length=ys.length := by simp
  have hp : pos=(h+2)+(ys.reverse.length : Int)+4 := by simpa only [hl,pos] using hposition
  have hrght : Holds touched (h+2+3) (ys ++ [false,false]) := by
    have he : h+2+3=h+5 := by omega
    simpa only [he] using hright
  have hround := roundtrip touched (h+2) pos ys.reverse ys hxs hys hl hp hleft hm
    (by simpa [Int.add_assoc] using hz1) (by simpa [Int.add_assoc] using hz2) hrght
  have hround' : silentSegment machine (cfg 262 (pos-2) touched) (cfg 17 (pos+1) u)
      (2*ys.reverse.length+7) := by
    have he : h+2+2=h+4 := by omega
    simpa only [he,u] using hround
  have hbefore : touched (pos-1)=false := by
    have ht := holds_append_tail touched (h+5) ys [false,false] hright
    have he : h+5+(ys.length : Int)=pos-1 := by omega
    rw [he] at ht
    exact ht.1
  have hu0 : u pos=false := by
    simp [u,touched,setAt,clearAt,show pos≠h+4 by omega,show pos≠h+2 by omega]
  have horigFrame : ∀ q, separator≤q → original q=t q := by
    intro q hq
    by_cases he : q=pos
    · subst q; simp [original,setAt,htargetOne]
    · simp [original,u,touched,setAt,clearAt,he,show q≠h+4 by omega,show q≠h+2 by omega]
  have horigleft : original (pos-1)=false := by
    simp [original,u,setAt,clearAt,show pos-1≠pos by omega,
      show pos-1≠h+4 by omega,show pos-1≠h+2 by omega,hbefore]
  have horigbank : Holds original pos (encode ((v+1)::vs) ++ [false,false]) := by
    apply holds_transport t original _ _ htarget'
    intro q hq _
    exact (horigFrame q (by omega)).symm
  obtain ⟨hresult,hframe,hshift⟩ := shift_bank_with_blank v vs pos original horigleft horigbank
  have hreset : clearAt pos original=u := by
    funext q
    by_cases he : q=pos
    · subst q; simp [clearAt,hu0]
    · simp [original,clearAt,setAt,he]
  have hone : original pos=true := by simp [original,setAt]
  have hfirst : machine.step (cfg 13 pos original)=(cfg 17 (pos+1) u,false) := by
    simpa only [hreset] using step13_1 pos original hone
  have hshift' : silentSegment machine (cfg 17 (pos+1) u) (cfg 23 (pos-2) out)
      (2*suffix.length+7) := by
    apply silent_tail machine (cfg 13 pos original) (cfg 17 (pos+1) u)
      (cfg 23 (pos-2) out) (2*suffix.length+7) hfirst
    simpa [suffix,f,out,Nat.add_assoc] using hshift
  have hpre := segAdd machine _ _ _ (k+(encode values).length+5) (2*ys.reverse.length+7) hscan hround'
  have hall := segAdd machine _ _ _ (k+(encode values).length+5+(2*ys.reverse.length+7))
    (2*suffix.length+7) hpre hshift'
  change Holds out pos (encode (v::vs) ++ [true,false,false]) ∧
    (∀ q, q<h+2 → out q=t q) ∧
    (∀ q, separator≤q → (q<pos ∨ f<q) → out q=t q) ∧
    silentSegment machine (cfg 280 (h+3) t) (cfg 23 (pos-2) out)
      (k+(encode values).length+5+(2*ys.reverse.length+7)+(2*suffix.length+7))
  refine ⟨hresult,?_,?_,hall⟩
  · intro q hq
    have hf : out q=original q := hframe q (Or.inl (by omega))
    rw [hf]
    simp [original,u,touched,setAt,clearAt,show q≠pos by omega,
      show q≠h+4 by omega,show q≠h+2 by omega]
  · intro q hq hq2
    have hf : out q=original q := hframe q hq2
    rw [hf]
    exact horigFrame q hq

#print axioms positive_touch_shift_280
end Shared.Beeping.NPcoNP.Native280Positive
