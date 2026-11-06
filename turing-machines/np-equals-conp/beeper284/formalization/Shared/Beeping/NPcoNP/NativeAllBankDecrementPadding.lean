import Shared.Beeping.NPcoNP.NativeAllBankDecrement
import Shared.Beeping.NPcoNP.NativeHalfBankFirst
import Shared.Beeping.NPcoNP.NativeIncBank
import Shared.Beeping.NPcoNP.NativeIncSelected

/-! Positive decrement retains an arbitrary suffix beyond its explicit
shift-and-reserve window. -/
namespace Shared.Beeping.NPcoNP.NativeAllBankDecrementPadding
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeAllBankDecrement
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem flat_length (xs : List Nat) :
    (xs.flatMap (fun z => false :: List.replicate (z+1) true)).length=(encode xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encode,block,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem positive_to1_padded (n : Fin 12) (h separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (rest : List Nat) (pad : List Bool) (hlen : values.length=n.val)
    (hlong : h+4≤separator) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1)
      ((encode values ++ (encode ((v+1)::rest) ++ [false,false])) ++ pad)) :
    let pos := separator+1+((encode values).length : Int)
    ∃ (steps : Nat) (out : Int → Bool), 0<steps ∧
      Holds out (separator+1) ((encode values ++ (encode (v::rest) ++ [true,false,false])) ++ pad) ∧
      out h=false ∧ out (h+1)=false ∧ out (h+2)=true ∧
      (∀ q, h+3≤q → q<separator → out q=true) ∧ out separator=false ∧
      (∀ q, q<pos → q≠h → q≠h+2 → out q=t q) ∧
      (∀ q, pos+2+((List.replicate v true ++ rest.flatMap
        (fun z => false :: List.replicate (z+1) true)).length : Int)<q → out q=t q) ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 1 (h-1) out) steps := by
  dsimp only
  let pos := separator+1+((encode values).length : Int)
  let old := encode values ++ (encode ((v+1)::rest) ++ [false,false])
  let new := encode values ++ (encode (v::rest) ++ [true,false,false])
  have hprefix : Holds t (separator+1) old := by
    apply holds_prefix t (separator+1) old pad
    exact bank
  have htail : Holds t (separator+1+((old.length : Nat) : Int)) pad :=
    holds_append_tail t (separator+1) old pad bank
  have hlenNew : new.length=old.length := by
    simp [new,old,encode,block_length]
    omega
  obtain ⟨steps,out,hs,hword,hz0,hz1,hmark,hones,hsep,hframe,hfar,_,hsegment⟩ :=
    positive_to1_exact n h separator t values v rest hlen hlong marker z1 z2 ones sep hprefix
  have htail' : Holds t (separator+1+((new.length : Nat) : Int)) pad := by
    simpa only [hlenNew] using htail
  have htailOut : Holds out (separator+1+((new.length : Nat) : Int)) pad := by
    apply holds_transport t out _ pad htail'
    intro q hq _
    have hlimit : pos+2+((List.replicate v true ++ rest.flatMap
        (fun z => false :: List.replicate (z+1) true)).length : Int)<q := by
      dsimp [pos,new] at *
      simp only [List.length_append,List.length_replicate,flat_length,encode,block_length,
        List.length_cons,List.length_nil,Nat.cast_add] at *
      push_cast at hq
      omega
    exact (hfar q hlimit).symm
  have hfull : Holds out (separator+1) (new ++ pad) :=
    holds_append_intro out (separator+1) new pad hword htailOut
  exact ⟨steps,out,hs,hfull,hz0,hz1,hmark,hones,hsep,hframe,hfar,hsegment⟩

#print axioms positive_to1_padded
end Shared.Beeping.NPcoNP.NativeAllBankDecrementPadding
