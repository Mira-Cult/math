import Shared.Beeping.NPcoNP.NativeAllBankScan
import Shared.Beeping.NPcoNP.NativeZeroRestoreGeneric
import Shared.Beeping.NPcoNP.NativePositiveGenericReturn

/-! Uniform zero and positive physical decrement branches for all producer
bank positions. The supplied tape windows and following control carry are
separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeAllBankDecrement
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Native279BankScan
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeZeroRestoreGeneric
open Shared.Beeping.NPcoNP.NativePositiveGenericReturn
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- A decrement entry reads a true marker and enters its indexed scanner
without changing the tape. -/
theorem decrement_entry (n : Fin 12) (h : Int) (t : Int → Bool)
    (marker : t h=true) :
    silentSegment machine (cfg (operationAt n false) h t)
      (cfg (scannerStart n) (h+1) t) 1 := by
  have hw : (cfg (operationAt n false) h t).write true=t := by
    funext q
    by_cases he : q=h
    · subst q; simpa [cfg,Config.write] using marker.symm
    · simp [cfg,Config.write,he]
  apply oneSeg machine _ _
  dsimp only [Machine.step,cfg]
  rw [marker,operation_entry_row]
  simpa only [Bool.not_false,cfg,Move.apply] using congrArg (fun u : Int → Bool =>
    ((⟨scannerStart n,h+1,u⟩ : Config 284),false)) hw

/-- For every bank position, the zero branch restores the complete bank,
changes the two stated control cells, and reaches state 25 silently. -/
theorem zero_to25 (n : Fin 12) (h separator : Int) (t : Int → Bool)
    (values : List Nat) (tail : List Bool) (hlen : values.length=n.val)
    (hlong : h+4≤separator) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ (block 0 ++ tail))) :
    let pos := separator+1+((encode values).length : Int)
    ∃ (steps : Nat) (out : Int → Bool), 0<steps ∧ out h=false ∧ out (h+2)=true ∧
      (∀ q, separator≤q → out q=t q) ∧ (∀ q, q<h → out q=t q) ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 25 (pos-1) out) steps := by
  dsimp only
  let base := h-2
  obtain ⟨q1,q2,q3,r0,r1,r2,chain⟩ := scanner_paths n
  have b2 : base+2=h := by dsimp [base]; omega
  have b3 : base+3=h+1 := by dsimp [base]; omega
  have b4 : base+4=h+2 := by dsimp [base]; omega
  have b5 : base+5=h+3 := by dsimp [base]; omega
  have hzero := zero_touch_restore_generic r0 r1 r2 chain base separator t values tail hlen
    (by dsimp [base]; omega) (by simpa only [b2] using marker)
    (by simpa only [b3] using z1) (by simpa only [b4] using z2)
    (by simpa only [b5] using ones) sep bank
  dsimp only at hzero
  obtain ⟨hright,hleft,hmark,hcarry,hseg⟩ := hzero
  let out := setAt (separator+1+((encode values).length : Int))
    (setAt (h+2) (clearAt h (clearAt (separator+1+((encode values).length : Int)) t)))
  let duration := (separator-(base+5)).toNat+(encode values).length+5+
    (2*(unaryBankPrefix (separator-(base+6)).toNat values).reverse.length+9)
  have hs : silentSegment machine (cfg (scannerStart n) (h+1) t)
      (cfg 25 (separator+1+((encode values).length : Int)-1) out) duration := by
    simpa only [b2,b3,b4,out,duration] using hseg
  refine ⟨1+duration,out,by omega,?_,?_,?_,?_,?_⟩
  · simpa only [b2,out,b4] using hmark
  · simpa only [b2,out,b4] using hcarry
  · simpa only [b2,out,b4] using hright
  · simpa only [b2,out,b4] using hleft
  · exact segAdd machine _ _ _ 1 duration (decrement_entry n h t marker) hs

/-- For every bank position, a positive target is decremented, the remaining
bank prefix is preserved, a zero reserve is appended, and the machine reaches
state 1 silently. The two trailing input blanks are explicit. -/
theorem positive_to1_exact (n : Fin 12) (h separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (rest : List Nat) (hlen : values.length=n.val)
    (hlong : h+4≤separator) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::rest) ++ [false,false]))) :
    let pos := separator+1+((encode values).length : Int)
    ∃ (steps : Nat) (out : Int → Bool), 0<steps ∧
      Holds out (separator+1) (encode values ++ (encode (v::rest) ++ [true,false,false])) ∧
      out h=false ∧ out (h+1)=false ∧ out (h+2)=true ∧
      (∀ q, h+3≤q → q<separator → out q=true) ∧ out separator=false ∧
      (∀ q, q<pos → q≠h → q≠h+2 → out q=t q) ∧
      (∀ q, pos+2+((List.replicate v true ++ rest.flatMap
        (fun z => false :: List.replicate (z+1) true)).length : Int)<q → out q=t q) ∧
      (∃ bound : Int, ∀ q, bound≤q → out q=t q) ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 1 (h-1) out) steps := by
  dsimp only
  let base := h-2
  let pos := separator+1+((encode values).length : Int)
  obtain ⟨q1,q2,q3,r0,r1,r2,chain⟩ := scanner_paths n
  have b1 : base+1=h-1 := by dsimp [base]; omega
  have b2 : base+2=h := by dsimp [base]; omega
  have b3 : base+3=h+1 := by dsimp [base]; omega
  have b4 : base+4=h+2 := by dsimp [base]; omega
  have b5 : base+5=h+3 := by dsimp [base]; omega
  obtain ⟨k,out,hk,htail,hm,hz,hcarry,hones,hsep,hframe,hfar,hbound,hseg⟩ :=
    positive_return_generic r0 r1 r2 chain base separator t values v rest hlen
      (by dsimp [base]; omega) (by simpa only [b2] using marker)
      (by simpa only [b3] using z1) (by simpa only [b4] using z2)
      (by simpa only [b5] using ones) sep bank
  have hpref : Holds t (separator+1) (encode values) :=
    holds_prefix_word t (separator+1) _ _ bank
  have hprefout : Holds out (separator+1) (encode values) := by
    apply holds_transport t out (separator+1) (encode values) hpref
    intro q hq hq'
    have hpos : q<pos := by dsimp [pos]; omega
    have he := hframe q (by simpa only [pos] using hpos) (by rw [b2]; omega) (by rw [b4]; omega)
    exact he.symm
  have hall := holds_append_intro out (separator+1) (encode values)
    (encode (v::rest) ++ [true,false,false]) hprefout (by simpa only [pos] using htail)
  have hs : silentSegment machine (cfg (scannerStart n) (h+1) t)
      (cfg 1 (h-1) out) k := by simpa only [b1,b3] using hseg
  refine ⟨1+k,out,by omega,hall,?_,?_,?_,?_,hsep,?_,?_,hbound,?_⟩
  · simpa only [b2] using hm
  · simpa only [b3] using hz
  · simpa only [b4] using hcarry
  · simpa only [b5] using hones
  · simpa only [b2,b4,pos] using hframe
  · simpa only [pos] using hfar
  · exact segAdd machine _ _ _ 1 k (decrement_entry n h t marker) hs

/-- Original positive-decrement interface. -/
theorem positive_to1 (n : Fin 12) (h separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (rest : List Nat) (hlen : values.length=n.val)
    (hlong : h+4≤separator) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::rest) ++ [false,false]))) :
    let pos := separator+1+((encode values).length : Int)
    ∃ (steps : Nat) (out : Int → Bool), 0<steps ∧
      Holds out (separator+1) (encode values ++ (encode (v::rest) ++ [true,false,false])) ∧
      out h=false ∧ out (h+1)=false ∧ out (h+2)=true ∧
      (∀ q, h+3≤q → q<separator → out q=true) ∧ out separator=false ∧
      (∀ q, q<pos → q≠h → q≠h+2 → out q=t q) ∧
      (∃ bound : Int, ∀ q, bound≤q → out q=t q) ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 1 (h-1) out) steps := by
  obtain ⟨steps,out,hs,hw,hz0,hz1,hmark,hones,hsep,hframe,_,hbound,hseg⟩ := positive_to1_exact n h separator t values v rest hlen hlong marker z1 z2 ones sep bank
  exact ⟨steps,out,hs,hw,hz0,hz1,hmark,hones,hsep,hframe,hbound,hseg⟩

#print axioms decrement_entry
#print axioms zero_to25
#print axioms positive_to1_exact
#print axioms positive_to1
end Shared.Beeping.NPcoNP.NativeAllBankDecrement
