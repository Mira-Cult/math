import Shared.Beeping.NPcoNP.NativeSecondZeroRestored
import Shared.Beeping.NPcoNP.NativeFirstReturn25

/-! Conditional finite return after the second zero-bank restoration. -/
namespace Shared.Beeping.NPcoNP.NativeSecondReturn25
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeFirstNextPath
open Shared.Beeping.NPcoNP.NativeFirstReturn25
open Shared.Beeping.NPcoNP.NativeSecondZeroRestored
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- The supplied first-event layout reaches the next state-1 carry entry,
with the row-2 path and bank preserved and exactly one event. -/
theorem supplied_beep_second_return (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+11≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (tail : List Bool)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      Holds out (h-4) nextPath ∧ (∀ q, q<h-4 → out q=false) ∧
      out (h+5)=false ∧ out (h+6)=false ∧ out (h+7)=false ∧
      (∀ q, h+8≤q → q<separator → out q=true) ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) ∧
      physical.advance (cfg 99 h t) n=cfg 1 (h+4) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,out,hn,hpath,hleft,h5,h6,h7,_h8,hcontrol,hframe,hbank,ha,hw⟩ :=
    supplied_beep_second_zero_restored_full h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero tail bank
  have hsep : out separator=false := by rw [hframe separator (le_refl _)]; exact hsepzero
  have hc : ∀ q, (h+4)+4≤q → q<separator → out q=true := by
    intro q hq hq2
    exact hcontrol q (by omega) hq2
  have hreturn := return25_to1_local (h+4) separator out tail (by omega)
    (by simpa [Int.add_assoc] using h5) (by simpa [Int.add_assoc] using h6)
    (by simpa [Int.add_assoc] using h7) hc hsep hbank
  let r := (separator-((h+4)+6)).toNat
  let ys := unaryBankPrefix r (List.replicate 5 0)
  change silentSegment machine (cfg 25 (separator+10) out) (cfg 1 (h+4) out) (ys.length+5) at hreturn
  obtain ⟨ha2,hw2⟩ := append_silent _ _ _ n (ys.length+5) ha hw hreturn
  exact ⟨n+(ys.length+5),out,by omega,hpath,hleft,h5,h6,h7,hcontrol,hframe,hbank,ha2,hw2⟩

#print axioms supplied_beep_second_return
end Shared.Beeping.NPcoNP.NativeSecondReturn25
