import Shared.Beeping.NPcoNP.Native54Cycle
import Shared.Beeping.NPcoNP.Native273Positive

/-! Conditional first-event execution through the positive eleventh block.
The supplied layout is not asserted reachable from a blank tape. -/
namespace Shared.Beeping.NPcoNP.NativeFifthPositive
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.Native54Cycle
open Shared.Beeping.NPcoNP.Native273Positive
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The supplied one-beep execution reaches a positive eleventh block,
decrements it and appends a zero reserve. The first ten encoded blocks are
unchanged. The first six are zero because prior physical operations require
that startup layout; the remaining four may contain arbitrary values. -/
theorem supplied_beep_fifth_positive (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+12≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (xs : List Nat) (hxs : xs.length=4)
    (v : Nat) (vs : List Nat)
    (bank : Holds t (separator+1)
      (encode (List.replicate 6 0 ++ xs) ++ (encode ((v+1)::vs) ++ [false,false]))) :
    let values := List.replicate 6 0 ++ xs
    let pos := separator+1+((encode values).length : Int)
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      Holds out (separator+1) (encode values) ∧
      Holds out pos (encode (v::vs) ++ [true,false,false]) ∧
      (∀ q, q<h-4 → out q=false) ∧
      physical.advance (cfg 99 h t) n=cfg 23 (pos-2) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  dsimp only
  let values := List.replicate 6 0 ++ xs
  let pos := separator+1+((encode values).length : Int)
  let rest := encode xs ++ (encode ((v+1)::vs) ++ [false,false])
  have hbankFirst : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ rest)) := by
    have he : values = List.replicate 5 0 ++ (0::xs) := by simp [values,List.replicate_succ]
    have hh := bank
    change Holds t (separator+1) (encode values ++ (encode ((v+1)::vs) ++ [false,false])) at hh
    rw [he,encode_append] at hh
    simpa [rest,encode,List.append_assoc] using hh
  obtain ⟨n,mid,hn,_hpath,hleft,hmark,hz1,hz2,hones,hframe,_hbank,ha,hw⟩ :=
    supplied_beep_fifth_prepared h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero rest hbankFirst
  have hsep : mid separator=false := by rw [hframe separator (le_refl _)]; exact hsepzero
  have hbankMid : Holds mid (separator+1)
      (encode values ++ (encode ((v+1)::vs) ++ [false,false])) := by
    apply holds_transport t mid _ _ bank
    intro q hq _
    exact (hframe q (by omega)).symm
  have hlen : values.length=10 := by simp [values,hxs]
  have hpositive := positive_touch_shift_273 (h+5) separator mid values v vs hlen
    (by omega) (by simpa [Int.add_assoc] using hmark)
    (by simpa [Int.add_assoc] using hz1) (by simpa [Int.add_assoc] using hz2)
    (by intro q hq hq2; exact hones q (by omega) hq2) hsep hbankMid
  let k := (separator-((h+5)+5)).toNat
  let r := (separator-((h+5)+6)).toNat
  let ys := unaryBankPrefix r values
  let touched := clearAt pos mid
  let u := setAt ((h+5)+4) (clearAt ((h+5)+2) touched)
  let original := setAt pos u
  let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  let f := pos+2+(suffix.length : Int)
  let out := spec original f (suffix.length+2)
  have hpos : separator+1≤pos := by dsimp [pos]; omega
  have hresult : Holds out pos (encode (v::vs) ++ [true,false,false]) := hpositive.1
  have hleftOut : ∀ q, q<h-4 → out q=false := by
    intro q hq
    have hf : out q=mid q := hpositive.2.1 q (by omega)
    rw [hf]
    exact hleft q hq
  have hbefore : Holds out (separator+1) (encode values) := by
    have hpref : Holds t (separator+1) (encode values) :=
      holds_prefix_word t (separator+1) _ (encode ((v+1)::vs) ++ [false,false]) bank
    apply holds_transport t out _ _ hpref
    intro q hq hq2
    have hqpos : q<pos := by dsimp [pos] at *; omega
    have hf : out q=mid q := hpositive.2.2.1 q (by omega) (Or.inl hqpos)
    rw [hf]
    exact (hframe q (by omega)).symm
  have hseg : silentSegment machine (cfg 273 (h+8) mid) (cfg 23 (pos-2) out)
      (k+(encode values).length+5+(2*ys.reverse.length+7)+(2*suffix.length+7)) := by
    have he : h+5+3=h+8 := by omega
    simpa only [he,k,r,ys,pos,touched,u,original,suffix,f,out] using hpositive.2.2.2
  obtain ⟨ha2,hw2⟩ := append_silent _ _ _ n
    (k+(encode values).length+5+(2*ys.reverse.length+7)+(2*suffix.length+7)) ha hw hseg
  exact ⟨n+_,out,by omega,hbefore,hresult,hleftOut,ha2,hw2⟩

#print axioms supplied_beep_fifth_positive
end Shared.Beeping.NPcoNP.NativeFifthPositive
