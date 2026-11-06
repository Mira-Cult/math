import Shared.Beeping.NPcoNP.NativeAllBankIncrementReturn
import Shared.Beeping.NPcoNP.NativeCarryBankFrame

/-! An increment, carry and selector reach a later parser while preserving the
updated bank. The graph successor and recurrent layout remain unproved. -/
namespace Shared.Beeping.NPcoNP.NativeAllBankIncrementNext
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeAllBankIncrementReturn
open Shared.Beeping.NPcoNP.NativeCarryBankFrame
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Under a supplied increment window and left blank tail, every physical
bank position reaches state 93 after silently increasing the selected value.
The updated bank and a finite left and right frame are preserved; the new
control word is not identified here. -/
theorem increment_to_next93 (n : Fin 12) (h z : Int) (t : Int → Bool) (k : Nat)
    (values : List Nat) (value : Nat) (rest : List Nat)
    (marker : t h=true) (hlen : values.length=n.val) (hk : 0<k)
    (h0 : t (h+1)=false) (h1 : t (h+2)=false)
    (control : ∀ i : Nat, i<k → t (h+3+(i : Int))=true)
    (delimiter : t (h+3+(k : Int))=false)
    (bank : Holds t (h+4+(k : Int)) (encode (values++value::rest) ++ [false]))
    (hz : z<h) (left : ∀ q, q≤z → t q=false) :
    let separator := h+3+(k : Int)
    let pos := separator+1+((encode values).length : Int)
    ∃ (steps : Nat) (out : Int → Bool) (mark finalHead : Int), 0<steps ∧
      mark≤h-1 ∧ out mark=true ∧ (∀ q, q<mark → out q=t q) ∧
      out (finalHead-1)=true ∧
      Holds out (separator+1) (encode (values++(value+1)::rest)) ∧
      (∀ q, pos+1+((value+(encode rest).length : Nat) : Int)<q → out q=t q) ∧
      silentSegment machine (cfg (operationAt n true) h t) (cfg 93 finalHead out) steps := by
  dsimp only
  let separator := h+3+(k : Int)
  let pos := separator+1+((encode values).length : Int)
  obtain ⟨a,mid,ha,hbank,_hzero,_hzero1,hmark,_hcontrol,hsep,hframe,hseg⟩ :=
    increment_to1 n h t k values value rest marker hlen hk h0 h1 control delimiter bank
  have hmleft : ∀ q, q≤z → mid q=false := by
    intro q hq
    have he : mid q=clearAt h t q := hframe q (by omega) (Or.inl (by omega))
    rw [he]
    simpa [clearAt,show q≠h by omega] using left q hq
  obtain ⟨b,out,mark,finalHead,hb,hm,houtmark,houtleft,hbankframe,hfinal,hcarry⟩ :=
    carry_selector_preserving_bank (h-1) (h+2) z separator mid hmleft (by omega) hmark
      (by dsimp [separator]; omega) (by simpa only [separator] using hsep)
  have houtbank : Holds out (separator+1) (encode (values++(value+1)::rest)) := by
    apply holds_transport mid out (separator+1) _
      (by simpa only [separator] using hbank)
    intro q hq _
    exact (hbankframe q (by omega)).symm
  have houtleft' : ∀ q, q<mark → out q=t q := by
    intro q hq
    rw [houtleft q hq]
    have he : mid q=clearAt h t q := hframe q (by omega) (Or.inl (by omega))
    rw [he]
    simp [clearAt,show q≠h by omega]
  have houtfar : ∀ q, pos+1+((value+(encode rest).length : Nat) : Int)<q → out q=t q := by
    intro q hq
    rw [hbankframe q (by dsimp [pos] at hq; omega)]
    have he : mid q=clearAt h t q := hframe q (by dsimp [pos,separator] at hq; omega) (Or.inr (by simpa only [pos,separator] using hq))
    rw [he]
    simp [clearAt,show q≠h by dsimp [pos,separator] at hq; omega]
  exact ⟨a+b,out,mark,finalHead,by omega,hm,houtmark,houtleft',hfinal,
    by simpa only [separator] using houtbank,by simpa only [pos,separator] using houtfar,
    segAdd machine _ _ _ a b hseg hcarry⟩

#print axioms increment_to_next93
end Shared.Beeping.NPcoNP.NativeAllBankIncrementNext
