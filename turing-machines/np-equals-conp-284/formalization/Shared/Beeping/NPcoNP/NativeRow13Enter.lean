import Shared.Beeping.NPcoNP.NativeRow13Selector
import Shared.Beeping.NPcoNP.NativeHalfState16Progress

/-! Entering the native-half scanner after its long-gap preparation. -/
namespace Shared.Beeping.NPcoNP.NativeRow13Enter
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeRow12Carry
open Shared.Beeping.NPcoNP.NativeRow13Dispatch
open Shared.Beeping.NPcoNP.NativeRow13Prepare
open Shared.Beeping.NPcoNP.NativeRow13Selector
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- The marked state-74 transition enters the state-46 scanner silently. -/
theorem step74_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 74 h t)=(cfg 46 (h+1) (clearAt h t),false) := by
  have row : machine.table.row 74 true=⟨false,.right,46,false⟩ := by decide
  have hw : (⟨74,h,t⟩ : Config 284).write false=clearAt h t := rfl
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

/-- A supplied row-13 path and long-gap frame enter state 46 after a
finite silent segment. The encoded data suffix is unchanged. -/
theorem enter_scanner (h separator : Int) (t : Int → Bool)
    (hlong : h+14≤separator) (path : Holds t (h-4) nextPath)
    (left : ∀ q, q<h-4 → t q=false)
    (gap : ∀ q, h+7<q → q<separator-1 → t q=false)
    (marker : t (separator-1)=true) :
    let u := fillRange (setAt (h+10) t) (h+12) (separator-1)
    let out := clearAt (h+10) u
    ∃ k : Nat, 0<k ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (h-3) t) (cfg 46 (h+11) out) k := by
  dsimp only
  let u := fillRange (setAt (h+10) t) (h+12) (separator-1)
  let out := clearAt (h+10) u
  obtain ⟨k,hk,hmark,hleft,hframe,hprep⟩ := row13_prepare h separator t hlong path gap marker
  have hp : Holds u (h-4) nextPath := by
    apply holds_transport t u _ _ path
    intro q hq hq'
    have hq10 : q<h+10 := by simp [nextPath] at hq'; omega
    exact (hleft q hq10).symm
  have hl : ∀ q, q<h-4 → u q=false := by
    intro q hq
    exact (hleft q (by omega)).trans (left q hq)
  have h11 : u (h+11)=false := by
    have hh := gap (h+11) (by omega) (by omega)
    simpa [u,fillRange,setAt] using hh
  let m := (separator-(h+14)).toNat
  have hm : (m : Int)=separator-(h+14) := Int.toNat_of_nonneg (by omega)
  have hones : ∀ q, h+12≤q → q≤h+11+(m : Int) → u q=true := by
    intro q hq hq'
    simp [u,fillRange,hq,show q<separator-1 by omega]
  have hs := selector_return h m u hp hl hmark h11 hones
  have hs' : silentSegment machine (cfg 83 (separator-3) u) (cfg 93 (h-3) u) (m+34) := by
    have he : h+11+(m : Int)=separator-3 := by omega
    simpa only [he] using hs
  have hd := dispatch_row13_path h u hp
  have he := oneSeg machine _ _ (step74_one (h+10) u hmark)
  have he' : silentSegment machine (cfg 74 (h+10) u) (cfg 46 (h+11) out) 1 := by
    simpa only [show h+10+1=h+11 by omega,out] using he
  have hf : ∀ q, separator≤q → out q=t q := by
    intro q hq
    simpa [out,clearAt,show q≠h+10 by omega] using hframe q hq
  have s1 := segAdd machine _ _ _ k (m+34) hprep hs'
  have s2 := segAdd machine _ _ _ (k+(m+34)) 13 s1 hd
  exact ⟨k+(m+34)+13+1,by omega,hf,
    segAdd machine _ _ _ (k+(m+34)+13) 1 s2 he'⟩

#print axioms step74_one
#print axioms enter_scanner
end Shared.Beeping.NPcoNP.NativeRow13Enter
