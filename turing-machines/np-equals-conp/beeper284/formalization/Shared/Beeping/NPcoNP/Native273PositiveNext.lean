import Shared.Beeping.NPcoNP.Native273PositiveFrame
import Shared.Beeping.NPcoNP.NativeBankReturn23Generic
import Shared.Beeping.NPcoNP.NativeFifthCarryPath

/-! Positive bank operation through the next literal dispatch. The finite
layout and blank right tail are explicit; no blank-start claim is made. -/
namespace Shared.Beeping.NPcoNP.Native273PositiveNext
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Native273Positive
open Shared.Beeping.NPcoNP.Native273PositiveFrame
open Shared.Beeping.NPcoNP.NativeBankReturn23Generic
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.NativeFifthNextPath
open Shared.Beeping.NPcoNP.NativeFifthCarryPath
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- For arbitrary ten-value prefixes and a positive target, the complete
bank update, return, carry, selector and literal dispatch terminate silently
at state 51. The updated bank word and the sixth prepared path are retained. -/
theorem positive_to_sixth_dispatch_suffix_frame (h b separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (vs : List Nat) (hlen : values.length=10)
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, b≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::vs) ++ [false,false]))) :
    let pos := separator+1+((encode values).length : Int)
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      Holds out (h-4) sixthPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.0.inc",12) ∧
      Holds out (separator+1) (encode values ++ (encode (v::vs) ++ [true,false,false])) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+6<q → q<separator-1 → out q=false) ∧ out (separator-1)=true ∧ out separator=false ∧
      (∀ q, pos+3+((List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)).length : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 51 (h+8) out) n := by
  dsimp only
  let pos := separator+1+((encode values).length : Int)
  let k := (separator-((h+5)+5)).toNat
  let r := (separator-((h+5)+6)).toNat
  let ys := unaryBankPrefix r values
  let touched := clearAt pos t
  let u := setAt ((h+5)+4) (clearAt ((h+5)+2) touched)
  let original := setAt pos u
  let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  let f := pos+2+(suffix.length : Int)
  let mid := spec original f (suffix.length+2)
  have hpos : separator+1≤pos := by dsimp [pos]; omega
  have hpositive := positive_touch_shift_273 (h+5) separator t values v vs hlen
    (by omega) (by simpa [Int.add_assoc] using mark) (by simpa [Int.add_assoc] using z1)
    (by simpa [Int.add_assoc] using z2) (by intro q hq hq2; exact ones q (by omega) hq2) sep bank
  have hframe := positive_control_frame (h+5) separator t values v vs hlen
    (by omega) (by simpa [Int.add_assoc] using mark) (by simpa [Int.add_assoc] using z1)
    (by simpa [Int.add_assoc] using z2) (by intro q hq hq2; exact ones q (by omega) hq2) sep bank
  have hp : Holds mid (h-4) fifthPath := by
    apply holds_transport t mid _ _ path
    intro q _ hq
    have hq' : q<h+7 := by simp [fifthPath] at hq; omega
    have hf : mid q=t q := hframe.2.2.2.2.2.1 q (by omega) (by omega) (by omega)
    exact hf.symm
  have hleft : ∀ q, q<h-4 → mid q=false := by
    intro q hq
    have hf : mid q=t q := hframe.2.2.2.2.2.1 q (by omega) (by omega) (by omega)
    rw [hf]
    exact left q hq
  have ht7 : mid ((h+5)+2)=false := hframe.1
  have ht8 : mid ((h+5)+3)=false := hframe.2.1
  have ht9 : mid ((h+5)+4)=true := hframe.2.2.1
  have h7 : mid (h+7)=false := by
    have he : h+5+2=h+7 := by omega
    simpa only [he] using ht7
  have h8 : mid (h+8)=false := by
    have he : h+5+3=h+8 := by omega
    simpa only [he] using ht8
  have h9 : mid (h+9)=true := by
    have he : h+5+4=h+9 := by omega
    simpa only [he] using ht9
  have hcontrol : ∀ q, h+9≤q → q<separator → mid q=true := by
    intro q hq hq2
    by_cases he : q=h+9
    · simpa only [he] using h9
    · exact hframe.2.2.2.1 q (by omega) hq2
  have hsep : mid separator=false := hframe.2.2.2.2.1
  have hpref : Holds t (separator+1) (encode values) :=
    holds_prefix_word t (separator+1) (encode values) _ bank
  have hpref' : Holds mid (separator+1) (encode values) := by
    apply holds_transport t mid _ _ hpref
    intro q hq hq2
    have hqpos : q<pos := by dsimp [pos] at *; omega
    have hf : mid q=t q := hframe.2.2.2.2.2.1 q hqpos (by omega) (by omega)
    exact hf.symm
  have hresult : Holds mid pos (encode (v::vs) ++ [true,false,false]) := hpositive.1
  have hbank : Holds mid (separator+1) (encode values ++ (encode (v::vs) ++ [true,false,false])) := by
    apply holds_append_intro mid (separator+1) (encode values) _ hpref'
    simpa only [pos] using hresult
  let rr := (separator-((h+6)+5)).toNat
  let yy := unaryBankPrefix rr values
  have hreturn := return23_generic (h+6) separator mid values
    (encode (v::vs) ++ [true,false,false]) (by omega)
    (by simpa [Int.add_assoc] using h7) (by simpa [Int.add_assoc] using h8)
    (by simpa [Int.add_assoc] using h9)
    (by intro q hq hq2; exact hcontrol q (by omega) hq2) hsep hbank
  have hreturn' : silentSegment machine (cfg 23 (pos-2) mid) (cfg 1 (h+6) mid) (yy.length+3) := by
    have he : separator+((encode values).length : Int)-1=pos-2 := by dsimp [pos]; omega
    simpa only [he,rr,yy] using hreturn
  have hpositiveFrame : ∀ q, separator≤q → (q<pos ∨ f<q) → mid q=t q := hpositive.2.2.1
  let bound := max b (f+1)
  have hfpos : pos≤f := by dsimp [f]; omega
  have hright : ∀ q, bound≤q → mid q=false := by
    intro q hq
    have hqB : b≤q := le_trans (le_max_left _ _) hq
    have hqF : f+1≤q := le_trans (le_max_right _ _) hq
    have hf : mid q=t q := hpositiveFrame q (by omega) (Or.inr (by omega))
    rw [hf]
    exact right q hqB
  obtain ⟨m,out,hm,hpath,hparse,hleft',hgap,hmarker,hsuffix,hcarry⟩ :=
    carry_to_sixth_path h bound separator mid hlong hp hleft h7 h8 hcontrol hsep hright
  have hbankOut : Holds out (separator+1) (encode values ++ (encode (v::vs) ++ [true,false,false])) := by
    apply holds_transport mid out _ _ hbank
    intro q hq _
    exact (hsuffix q (by omega)).symm
  have hstep := dispatch_sixth_path h out hpath
  have hbody : silentSegment machine (cfg 273 (h+8) t) (cfg 23 (pos-2) mid)
      (k+(encode values).length+5+(2*ys.reverse.length+7)+(2*suffix.length+7)) := by
    have he : h+5+3=h+8 := by omega
    simpa only [he,k,r,ys,pos,touched,u,original,suffix,f,mid] using hpositive.2.2.2
  have a := segAdd machine _ _ _ _ _ hbody hreturn'
  have bb := segAdd machine _ _ _ _ _ a hcarry
  have all := segAdd machine _ _ _ _ 11 bb hstep
  have hsepOut : out separator=false := by rw [hsuffix separator (by omega)]; exact hsep
  have htail : ∀ q, pos+3+(suffix.length : Int)≤q → out q=t q := by
    intro q hq
    rw [hsuffix q (by dsimp [pos] at hq; omega)]
    exact hpositiveFrame q (by dsimp [pos] at hq; omega) (Or.inr (by dsimp [f]; omega))
  exact ⟨_,out,by omega,hpath,hparse,hbankOut,hleft',hgap,hmarker,hsepOut,htail,all⟩


theorem positive_to_sixth_dispatch_full (h b separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (vs : List Nat) (hlen : values.length=10)
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, b≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::vs) ++ [false,false]))) :
    let pos := separator+1+((encode values).length : Int)
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      Holds out (h-4) sixthPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.0.inc",12) ∧
      Holds out (separator+1) (encode values ++ (encode (v::vs) ++ [true,false,false])) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+6<q → q<separator-1 → out q=false) ∧ out (separator-1)=true ∧ out separator=false ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 51 (h+8) out) n := by
  obtain ⟨n,out,hn,hpath,hparse,hbank,hleft,hgap,hmarker,hsep,_,hseg⟩ :=
    positive_to_sixth_dispatch_suffix_frame h b separator t values v vs hlen hlong
      path left mark z1 z2 ones sep right bank
  exact ⟨n,out,hn,hpath,hparse,hbank,hleft,hgap,hmarker,hsep,hseg⟩

/-- The previous framed interface, projecting away the separator fact. -/
theorem positive_to_sixth_dispatch_framed (h b separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (vs : List Nat) (hlen : values.length=10)
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, b≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::vs) ++ [false,false]))) :
    let pos := separator+1+((encode values).length : Int)
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      Holds out (h-4) sixthPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.0.inc",12) ∧
      Holds out (separator+1) (encode values ++ (encode (v::vs) ++ [true,false,false])) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+6<q → q<separator-1 → out q=false) ∧ out (separator-1)=true ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 51 (h+8) out) n := by
  obtain ⟨n,out,hn,hpath,hparse,hbank,hleft,hgap,hmarker,_,hseg⟩ :=
    positive_to_sixth_dispatch_full h b separator t values v vs hlen hlong
      path left mark z1 z2 ones sep right bank
  exact ⟨n,out,hn,hpath,hparse,hbank,hleft,hgap,hmarker,hseg⟩

/-- The original interface, projecting away the control-gap facts. -/
theorem positive_to_sixth_dispatch (h b separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (vs : List Nat) (hlen : values.length=10)
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, b≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::vs) ++ [false,false]))) :
    let pos := separator+1+((encode values).length : Int)
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      Holds out (h-4) sixthPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.0.inc",12) ∧
      Holds out (separator+1) (encode values ++ (encode (v::vs) ++ [true,false,false])) ∧
      (∀ q, q<h-4 → out q=false) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 51 (h+8) out) n := by
  obtain ⟨n,out,hn,hpath,hparse,hbank,hleft,_,_,hseg⟩ :=
    positive_to_sixth_dispatch_framed h b separator t values v vs hlen hlong
      path left mark z1 z2 ones sep right bank
  exact ⟨n,out,hn,hpath,hparse,hbank,hleft,hseg⟩

#print axioms positive_to_sixth_dispatch_suffix_frame
#print axioms positive_to_sixth_dispatch_full
#print axioms positive_to_sixth_dispatch_framed
#print axioms positive_to_sixth_dispatch
end Shared.Beeping.NPcoNP.Native273PositiveNext
