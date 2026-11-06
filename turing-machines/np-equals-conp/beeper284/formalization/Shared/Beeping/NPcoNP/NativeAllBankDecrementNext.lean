import Shared.Beeping.NPcoNP.NativeAllBankDecrement
import Shared.Beeping.NPcoNP.NativeCarryBankFrame
import Shared.Beeping.NPcoNP.NativeBankReturnGeneric

/-! The positive decrement branch, carry and selector return to state 93
while preserving the updated bank. The graph successor remains separate. -/
namespace Shared.Beeping.NPcoNP.NativeAllBankDecrementNext
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.Native279BankScan
open Shared.Beeping.NPcoNP.NativeZeroRestoreGeneric
open Shared.Beeping.NPcoNP.NativeBankReturnGeneric
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeAllBankDecrement
open Shared.Beeping.NPcoNP.NativeCarryBankFrame
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- For every physical bank position, a supplied positive-decrement window
and left blank tail lead silently back to state 93 with the decremented bank
and a zero reserve. The resulting grammar control path is not identified. -/
theorem positive_to_next93 (n : Fin 12) (h z separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (rest : List Nat) (hlen : values.length=n.val)
    (hlong : h+4≤separator) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::rest) ++ [false,false])))
    (hz : z<h) (left : ∀ q, q≤z → t q=false) :
    ∃ (steps : Nat) (out : Int → Bool) (mark finalHead : Int), 0<steps ∧
      mark≤h-1 ∧ out mark=true ∧ (∀ q, q<mark → out q=t q) ∧
      out (finalHead-1)=true ∧
      Holds out (separator+1) (encode values ++ (encode (v::rest) ++ [true,false,false])) ∧
      (∃ bound : Int, ∀ q, bound≤q → out q=t q) ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 93 finalHead out) steps := by
  let pos := separator+1+((encode values).length : Int)
  obtain ⟨a,mid,ha,hbank,_hm,_hz,hmark,_hones,hsep,hframe,hbound,hseg⟩ :=
    positive_to1 n h separator t values v rest hlen hlong marker z1 z2 ones sep bank
  have hmleft : ∀ q, q≤z → mid q=false := by
    intro q hq
    rw [hframe q (by omega) (by omega) (by omega)]
    exact left q hq
  obtain ⟨b,out,mark,finalHead,hb,hmarkle,houtmark,houtleft,hbankframe,hfinal,hcarry⟩ :=
    carry_selector_preserving_bank (h-1) (h+2) z separator mid hmleft (by omega) hmark
      (by omega) hsep
  have houtbank : Holds out (separator+1)
      (encode values ++ (encode (v::rest) ++ [true,false,false])) := by
    apply holds_transport mid out (separator+1) _ hbank
    intro q hq _
    exact (hbankframe q (by omega)).symm
  have houtleft' : ∀ q, q<mark → out q=t q := by
    intro q hq
    rw [houtleft q hq]
    exact hframe q (by omega) (by omega) (by omega)
  obtain ⟨bound,hfar⟩ := hbound
  have houtfar : ∀ q, max bound separator≤q → out q=t q := by
    intro q hq
    rw [hbankframe q (le_trans (le_max_right _ _) hq)]
    exact hfar q (le_trans (le_max_left _ _) hq)
  exact ⟨a+b,out,mark,finalHead,by omega,hmarkle,houtmark,houtleft',hfinal,houtbank,
    ⟨max bound separator,houtfar⟩,segAdd machine _ _ _ a b hseg hcarry⟩

/-- The zero branch and its bank return reach state 1 without changing the
bank. The additional blank immediately left of the entry marker is explicit. -/
theorem zero_to1_exact (n : Fin 12) (h separator : Int) (t : Int → Bool)
    (values : List Nat) (tail : List Bool) (hlen : values.length=n.val)
    (hlong : h+4≤separator) (marker : t h=true) (prev : t (h-1)=false)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ (block 0 ++ tail))) :
    ∃ (steps : Nat) (out : Int → Bool), 0<steps ∧ out (h+2)=true ∧ out separator=false ∧
      out h=false ∧ out (h+1)=false ∧ (∀ q, h+2≤q → q<separator → out q=true) ∧
      (∀ q, separator≤q → out q=t q) ∧ (∀ q, q<h → out q=t q) ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 1 (h-2) out) steps := by
  let base := h-2
  let pos := separator+1+((encode values).length : Int)
  let out := setAt pos (setAt (h+2) (clearAt h (clearAt pos t)))
  obtain ⟨q1,q2,q3,r0,r1,r2,chain⟩ := scanner_paths n
  have b1 : base+1=h-1 := by dsimp [base]; omega
  have b2 : base+2=h := by dsimp [base]; omega
  have b3 : base+3=h+1 := by dsimp [base]; omega
  have b4 : base+4=h+2 := by dsimp [base]; omega
  have b5 : base+5=h+3 := by dsimp [base]; omega
  have hz := zero_touch_restore_generic r0 r1 r2 chain base separator t values tail hlen
    (by dsimp [base]; omega) (by simpa only [b2] using marker)
    (by simpa only [b3] using z1) (by simpa only [b4] using z2)
    (by simpa only [b5] using ones) sep bank
  dsimp only at hz
  obtain ⟨hright,hleft,hzero,hcarry,hscan⟩ := hz
  have hright' : ∀ q, separator≤q → out q=t q := by simpa only [b2,b4,out,pos] using hright
  have hleft' : ∀ q, q<h → out q=t q := by simpa only [b2,b4,out,pos] using hleft
  have hzero' : out h=false := by simpa only [b2,b4,out,pos] using hzero
  have hcarry' : out (h+2)=true := by simpa only [b2,b4,out,pos] using hcarry
  have hprev : out (h-1)=false := (hleft' _ (by omega)).trans prev
  have hz1 : out (h+1)=false := by
    simp [out,pos,setAt,clearAt,show h+1≠h+2 by omega,
      show h+1≠h by omega,show h+1≠separator+1+((encode values).length : Int) by omega,z1]
  have hon : ∀ q, h+2≤q → q<separator → out q=true := by
    intro q hq hq'
    by_cases he : q=h+2
    · simpa only [he] using hcarry'
    · have hqt : t q=true := ones q (by omega) hq'
      simp [out,pos,setAt,clearAt,he,show q≠h by omega,
        show q≠separator+1+((encode values).length : Int) by omega,hqt]
  have houtsep : out separator=false := (hright' _ (le_refl _)).trans sep
  have houtbank : Holds out (separator+1) (encode values ++ (block 0 ++ tail)) := by
    apply holds_transport t out (separator+1) _ bank
    intro q hq _
    exact (hright' q (by omega)).symm
  have hret := return25_generic_min_gap (h-2) separator out values (block 0 ++ tail)
    (by omega) (by simpa only [show h-2+1=h-1 by omega] using hprev)
    (by simpa only [show h-2+2=h by omega] using hzero')
    (by simpa only [show h-2+3=h+1 by omega] using hz1)
    (by simpa only [show h-2+4=h+2 by omega] using hon) houtsep houtbank
  let d := (separator-(base+5)).toNat+(encode values).length+5+
    (2*(unaryBankPrefix (separator-(base+6)).toNat values).reverse.length+9)
  have hscan' : silentSegment machine (cfg (scannerStart n) (h+1) t)
      (cfg 25 (separator+((encode values).length : Int)) out) d := by
    have he : separator+1+((encode values).length : Int)-1=separator+((encode values).length : Int) := by omega
    simpa only [b2,b3,b4,out,pos,d,he] using hscan
  have hfirst := segAdd machine _ _ _ 1 d (decrement_entry n h t marker) hscan'
  refine ⟨(1+d)+((unaryBankPrefix (separator-(h-2+6)).toNat values).length+5),out,
    by omega,hcarry',houtsep,hzero',hz1,hon,hright',hleft',?_⟩
  exact segAdd machine _ _ _ _ _ hfirst hret


/-- Projection retaining the original zero-branch return interface. -/
theorem zero_to1 (n : Fin 12) (h separator : Int) (t : Int → Bool)
    (values : List Nat) (tail : List Bool) (hlen : values.length=n.val)
    (hlong : h+4≤separator) (marker : t h=true) (prev : t (h-1)=false)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ (block 0 ++ tail))) :
    ∃ (steps : Nat) (out : Int → Bool), 0<steps ∧ out (h+2)=true ∧ out separator=false ∧
      (∀ q, separator≤q → out q=t q) ∧ (∀ q, q<h → out q=t q) ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 1 (h-2) out) steps := by
  obtain ⟨steps,out,hsteps,hmark,hsep,_hz,_hz1,_hones,hright,hleft,hseg⟩ :=
    zero_to1_exact n h separator t values tail hlen hlong marker prev z1 z2 ones sep bank
  exact ⟨steps,out,hsteps,hmark,hsep,hright,hleft,hseg⟩

/-- The zero branch, bank return and carry reach state 93 silently, preserving
the entire bank. The destination control word is not identified. -/
theorem zero_to_next93 (n : Fin 12) (h z separator : Int) (t : Int → Bool)
    (values : List Nat) (tail : List Bool) (hlen : values.length=n.val)
    (hlong : h+4≤separator) (marker : t h=true) (prev : t (h-1)=false)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ (block 0 ++ tail)))
    (hz : z<h-2) (left : ∀ q, q≤z → t q=false) :
    ∃ (steps : Nat) (out : Int → Bool) (mark finalHead : Int), 0<steps ∧
      mark≤h-2 ∧ out mark=true ∧ (∀ q, q<mark → out q=t q) ∧
      out (finalHead-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 93 finalHead out) steps := by
  obtain ⟨a,mid,ha,hmark,hsep,hright,hleft,hseg⟩ :=
    zero_to1 n h separator t values tail hlen hlong marker prev z1 z2 ones sep bank
  have hmleft : ∀ q, q≤z → mid q=false := by
    intro q hq
    rw [hleft q (by omega)]
    exact left q hq
  obtain ⟨b,out,mark,finalHead,hb,hm,houtmark,houtleft,hbankframe,hfinal,hcarry⟩ :=
    carry_selector_preserving_bank (h-2) (h+2) z separator mid hmleft (by omega) hmark
      (by omega) hsep
  have houtleft' : ∀ q, q<mark → out q=t q := by
    intro q hq
    rw [houtleft q hq,hleft q (by omega)]
  have houtbank : ∀ q, separator≤q → out q=t q := by
    intro q hq
    rw [hbankframe q hq,hright q hq]
  exact ⟨a+b,out,mark,finalHead,by omega,hm,houtmark,houtleft',hfinal,houtbank,
    segAdd machine _ _ _ a b hseg hcarry⟩

#print axioms zero_to1_exact
#print axioms zero_to1
#print axioms zero_to_next93
#print axioms positive_to_next93
end Shared.Beeping.NPcoNP.NativeAllBankDecrementNext
