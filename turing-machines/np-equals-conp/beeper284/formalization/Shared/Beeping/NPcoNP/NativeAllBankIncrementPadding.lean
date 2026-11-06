import Shared.Beeping.NPcoNP.NativeAllBankIncrementReturn
import Shared.Beeping.NPcoNP.NativeHalfBankFirst
import Shared.Beeping.NPcoNP.NativeIncBank
import Shared.Beeping.NPcoNP.NativeIncSelected

/-! The uniform increment preserves an arbitrary suffix beyond the blank cell
consumed by the shifted bank. -/
namespace Shared.Beeping.NPcoNP.NativeAllBankIncrementPadding
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeAllBankIncrementReturn
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem increment_to1_padded (n : Fin 12) (h : Int) (t : Int → Bool) (k : Nat)
    (values : List Nat) (value : Nat) (rest : List Nat) (pad : List Bool)
    (marker : t h=true) (hlen : values.length=n.val) (hk : 0<k)
    (h0 : t (h+1)=false) (h1 : t (h+2)=false)
    (control : ∀ i : Nat, i<k → t (h+3+(i : Int))=true)
    (delimiter : t (h+3+(k : Int))=false)
    (bank : Holds t (h+4+(k : Int)) ((encode (values++value::rest) ++ [false]) ++ pad)) :
    let separator := h+3+(k : Int)
    let pos := separator+1+((encode values).length : Int)
    ∃ (steps : Nat) (out : Int → Bool), 0<steps ∧
      Holds out (separator+1) (encode (values++(value+1)::rest) ++ pad) ∧
      out h=false ∧ out (h+1)=false ∧ out (h+2)=true ∧
      (∀ q, h+3≤q → q<separator → out q=true) ∧ out separator=false ∧
      (∀ q, q≠h+2 → (q<pos+1 ∨ pos+1+((value+(encode rest).length : Nat) : Int)<q) →
        out q=clearAt h t q) ∧
      silentSegment machine (cfg (operationAt n true) h t) (cfg 1 (h-1) out) steps := by
  dsimp only
  let separator := h+3+(k : Int)
  let pos := separator+1+((encode values).length : Int)
  let old := encode (values++value::rest) ++ [false]
  let new := encode (values++(value+1)::rest)
  have hprefix : Holds t (h+4+(k : Int)) old := by
    apply holds_prefix t (h+4+(k : Int)) old pad
    exact bank
  have htail : Holds t (h+4+(k : Int)+((old.length : Nat) : Int)) pad :=
    holds_append_tail t (h+4+(k : Int)) old pad bank
  have hlenNew : new.length=old.length := by
    simp [new,old,encode_append,encode,block_length]
    omega
  obtain ⟨steps,out,hs,hword,hz0,hz1,hmark,hcontrol,hsep,hframe,hsegment⟩ :=
    increment_to1 n h t k values value rest marker hlen hk h0 h1 control delimiter hprefix
  have htailOut : Holds out (separator+1+((new.length : Nat) : Int)) pad := by
    have he : h+4+(k : Int)+((old.length : Nat) : Int)=separator+1+((new.length : Nat) : Int) := by
      rw [hlenNew]
      dsimp [separator]
      omega
    have htail' : Holds t (separator+1+((new.length : Nat) : Int)) pad := by simpa only [he] using htail
    apply holds_transport t out _ pad htail'
    intro q hq _
    have hlimit : pos+1+((value+(encode rest).length : Nat) : Int)<q := by
      dsimp [pos,separator,new] at *
      simp only [encode_append,List.length_append,encode,block_length,Nat.cast_add] at hq
      push_cast at hq
      omega
    have he : out q=clearAt h t q := hframe q (by dsimp [pos,separator] at *; omega) (Or.inr hlimit)
    rw [he]
    simp [clearAt,show q≠h by dsimp [pos,separator] at *; omega]
  have hfull : Holds out (separator+1) (new ++ pad) :=
    holds_append_intro out (separator+1) new pad hword htailOut
  exact ⟨steps,out,hs,hfull,hz0,hz1,hmark,hcontrol,hsep,hframe,hsegment⟩

#print axioms increment_to1_padded
end Shared.Beeping.NPcoNP.NativeAllBankIncrementPadding
