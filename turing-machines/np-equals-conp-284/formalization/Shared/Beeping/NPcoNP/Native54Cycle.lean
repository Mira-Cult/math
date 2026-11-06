import Shared.Beeping.NPcoNP.Native54Redispatch

/-! Exact conditional preparation and redispatch for state 54. -/
namespace Shared.Beeping.NPcoNP.Native54Cycle
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.Native54Prepare
open Shared.Beeping.NPcoNP.Native54Redispatch
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

/-- The initial zero branch is followed by redispatch on a one and reaches
state 273 in exactly `2*r+47` silent steps, without changing the path or the
tape to the right of the marker. -/
theorem prepare_and_redispatch (h : Int) (r : Nat) (t : Int → Bool)
    (hw : Holds t (h-4) fifthPath) (left : ∀ q, q<h-4 → t q=false)
    (gap : ∀ q, h+4<q → q<h+11+(r : Int) → t q=false)
    (marker : t (h+11+(r : Int))=true) :
    let u := fillRange (setAt (h+7) t) (h+10) (h+11+(r : Int))
    (∀ q, h+11+(r : Int)≤q → u q=t q) ∧
    Holds u (h-4) fifthPath ∧ u (h+7)=true ∧
    silentSegment machine (cfg 54 (h+7) t) (cfg 273 (h+8) u) (2*r+47) := by
  dsimp only
  let u := fillRange (setAt (h+7) t) (h+10) (h+11+(r : Int))
  have h0 : t (h+7)=false := gap _ (by omega) (by omega)
  have h1 : t (h+8)=false := gap _ (by omega) (by omega)
  have h2 : t (h+9)=false := gap _ (by omega) (by omega)
  have hz : ∀ i : Nat, i<r+1 → t (h+7+3+(i : Int))=false := by
    intro i hi
    apply gap <;> omega
  have hm : t (h+7+3+((r+1 : Nat) : Int))=true := by
    convert marker using 1 <;> congr 1 <;> push_cast <;> omega
  obtain ⟨_hu,_frame,hprep⟩ := zero_prepare_to83 (h+7) t (r+1) (by omega) h0
    (by simpa [Int.add_assoc] using h1) (by simpa [Int.add_assoc] using h2) hz hm
  have prep : silentSegment machine (cfg 54 (h+7) t) (cfg 83 (h+9+(r : Int)) u) (r+6) := by
    have e1 : h+11+(r : Int)-2=h+9+(r : Int) := by omega
    have e2 : h+7+3=h+10 := by omega
    have e3 : h+10+((r+1 : Nat) : Int)=h+11+(r : Int) := by push_cast; omega
    have e4 : r+1+5=r+6 := by omega
    simpa only [e2,e3,e1,e4,u] using hprep
  have sel := selector_prepared h r t hw left h1 h2
  have hp : Holds u (h-4) fifthPath := by
    apply holds_transport t u _ _ hw
    intro q _ hq2
    have hq' : q<h+7 := by simp [fifthPath] at hq2; omega
    have hn : ¬ (h+10≤q ∧ q<h+11+(r : Int)) := by omega
    simp [u,fillRange,setAt,hn,show q≠h+7 by omega]
  have hd := dispatch_fifth_path h u hp
  have hone : u (h+7)=true := by simp [u,fillRange,setAt]
  have he := oneSeg machine _ _ (step54_one (h+7) u hone)
  have a := segAdd machine _ _ _ (r+6) (r+30) prep sel
  have b := segAdd machine _ _ _ (r+6+(r+30)) 10 a hd
  have c := segAdd machine _ _ _ (r+6+(r+30)+10) 1 b he
  refine ⟨?_,hp,hone,?_⟩
  · intro q hq
    have hn : ¬ (h+10≤q ∧ q<h+11+(r : Int)) := by omega
    simp [u,fillRange,setAt,hn,show q≠h+7 by omega]
  · have et : r+6+(r+30)+10+1=2*r+47 := by omega
    have eh : h+7+1=h+8 := by omega
    simpa only [et,eh] using c

/-- Composed with the prior conditional one-beep execution, preparation
reaches scanner state 273 with the prepared path and bank still intact. -/
theorem supplied_beep_fifth_prepared (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+12≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (tail : List Bool)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      Holds out (h-4) fifthPath ∧ (∀ q, q<h-4 → out q=false) ∧
      out (h+7)=true ∧ out (h+8)=false ∧ out (h+9)=false ∧
      (∀ q, h+10≤q → q<separator → out q=true) ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) ∧
      physical.advance (cfg 99 h t) n=cfg 273 (h+8) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,mid,hn,hpath,_hparse,hleft,hgap,hmarker,hframe,_hbank,ha,hw⟩ :=
    supplied_beep_fifth_dispatch h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      (by omega) ones left hb right hsepzero tail bank
  let r := (separator-(h+12)).toNat
  have hr : (r : Int)=separator-(h+12) := Int.toNat_of_nonneg (by omega)
  have hg : ∀ q, h+4<q → q<h+11+(r : Int) → mid q=false := by
    intro q hq hq2
    apply hgap q hq
    omega
  have hm : mid (h+11+(r : Int))=true := by
    have he : h+11+(r : Int)=separator-1 := by omega
    simpa only [he] using hmarker
  let out := fillRange (setAt (h+7) mid) (h+10) (h+11+(r : Int))
  have hprep := prepare_and_redispatch h r mid hpath hleft hg hm
  have houtleft : ∀ q, q<h+7 → out q=mid q := by
    intro q hq
    have hn : ¬ (h+10≤q ∧ q<h+11+(r : Int)) := by omega
    simp [out,fillRange,setAt,hn,show q≠h+7 by omega]
  have hleftOut : ∀ q, q<h-4 → out q=false := by
    intro q hq
    rw [houtleft q (by omega)]
    exact hleft q hq
  have hout8 : out (h+8)=false := by
    have hmid : mid (h+8)=false := hg _ (by omega) (by omega)
    simp [out,fillRange,setAt,show h+8≠h+7 by omega,hmid]
  have hout9 : out (h+9)=false := by
    have hmid : mid (h+9)=false := hg _ (by omega) (by omega)
    simp [out,fillRange,setAt,show h+9≠h+7 by omega,hmid]
  have houtones : ∀ q, h+10≤q → q<separator → out q=true := by
    intro q hq hq2
    by_cases hq3 : q<h+11+(r : Int)
    · have hin : h+10≤q ∧ q<h+11+(r : Int) := ⟨hq,hq3⟩
      simp [out,fillRange,hin]
    · have he : q=separator-1 := by omega
      subst q
      have hn : ¬ (h+10≤separator-1 ∧ separator-1<h+11+(r : Int)) := by omega
      simp [out,fillRange,setAt,hn,show separator-1≠h+7 by omega,hmarker]
  have hfinal : ∀ q, separator≤q → out q=t q := by
    intro q hq
    have hf : out q=mid q := hprep.1 q (by omega)
    rw [hf]
    exact hframe q hq
  have hbankFinal : Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) := by
    apply holds_transport t out _ _ bank
    intro q hq _
    exact (hfinal q (by omega)).symm
  obtain ⟨ha2,hw2⟩ := append_silent _ _ _ n (2*r+47) ha hw hprep.2.2.2
  exact ⟨n+(2*r+47),out,by omega,hprep.2.1,hleftOut,hprep.2.2.1,hout8,hout9,
    houtones,hfinal,hbankFinal,ha2,hw2⟩

#print axioms supplied_beep_fifth_prepared
#print axioms prepare_and_redispatch
end Shared.Beeping.NPcoNP.Native54Cycle
