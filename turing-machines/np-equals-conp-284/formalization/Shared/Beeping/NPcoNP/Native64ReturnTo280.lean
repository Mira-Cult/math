import Shared.Beeping.NPcoNP.Native64Redispatch
import Shared.Beeping.NPcoNP.NativeHalfScannerFrames

/-! State-64 preparation, selector and entry into the row-10 scanner. -/
namespace Shared.Beeping.NPcoNP.Native64ReturnTo280
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeFifthZeroNextPath
open Shared.Beeping.NPcoNP.Native64Prepare
open Shared.Beeping.NPcoNP.Native64Redispatch
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

/-- A supplied row-10 zero-gap layout completes its finite silent preparation,
rediscovers the same row-10 path and enters physical scanner state 280. -/
theorem prepare_and_enter_full (h separator : Int) (t : Int → Bool)
    (hlong : h+12≤separator) (path : Holds t (h-4) zeroNextPath)
    (left : ∀ q, q<h-4 → t q=false)
    (gap : ∀ q, h+5<q → q<separator-1 → t q=false)
    (marker : t (separator-1)=true) :
    let out := fillRange (setAt (h+8) t) (h+11) (separator-1)
    ∃ k : Nat, 0<k ∧ Holds out (h-4) zeroNextPath ∧
      (∀ q, q<h-4 → out q=false) ∧ out (h+8)=true ∧
      out (h+9)=false ∧ out (h+10)=false ∧
      (∀ q, h+11≤q → q<separator → out q=true) ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 64 (h+8) t) (cfg 280 (h+9) out) k := by
  dsimp only
  let r := (separator-(h+12)).toNat
  have hr : (r : Int)=separator-(h+12) := Int.toNat_of_nonneg (by omega)
  have h0 : t (h+8)=false := gap _ (by omega) (by omega)
  have h1 : t (h+8+1)=false := gap _ (by omega) (by omega)
  have h2 : t (h+8+2)=false := gap _ (by omega) (by omega)
  have hz : ∀ i : Nat, i<r → t (h+8+3+(i : Int))=false := by
    intro i hi
    apply gap <;> omega
  have hm : t (h+8+3+(r : Int))=true := by
    have he : h+8+3+(r : Int)=separator-1 := by omega
    rw [he]; exact marker
  let out := fillRange (setAt (h+8) t) (h+11) (separator-1)
  let duration := if r=0 then 7 else r+5
  let head := if r=0 then h+7 else separator-3
  have he : h+11+(r : Int)=separator-1 := by omega
  have hh : (if r=0 then h+8-1 else separator-1-2)=head := by
    dsimp [head]
    split_ifs <;> omega
  have hp := zero_prepare_to83_exact (h+8) t r h0 h1 h2 hz hm
  have hprep : silentSegment machine (cfg 64 (h+8) t) (cfg 83 head out) duration := by
    simpa only [show h+8+3=h+11 by omega,he,hh,out,duration] using hp
  have hbefore : ∀ q, q<h+8 → out q=t q := by
    intro q hq
    have hn : ¬ (h+11≤q ∧ q<separator-1) := by omega
    have hne : q≠h+8 := by omega
    simp [out,fillRange,setAt,hn,hne]
  have hpath : Holds out (h-4) zeroNextPath := by
    apply holds_transport t out _ _ path
    intro q hq hq'
    symm
    apply hbefore
    simp [zeroNextPath] at hq'
    omega
  have hleft : ∀ q, q<h-4 → out q=false := by
    intro q hq
    rw [hbefore q (by omega)]
    exact left q hq
  have h8 : out (h+8)=true := by simp [out,fillRange,setAt]
  have h9 : out (h+9)=false := by
    simp [out,fillRange,setAt,show ¬(h+11≤h+9 ∧ h+9<separator-1) by omega,
      show h+9≠h+8 by omega,show h+8+1=h+9 by omega] at h1 ⊢
    exact h1
  have h10 : out (h+10)=false := by
    simp [out,fillRange,setAt,show ¬(h+11≤h+10 ∧ h+10<separator-1) by omega,
      show h+10≠h+8 by omega,show h+8+2=h+10 by omega] at h2 ⊢
    exact h2
  have hframe : ∀ q, separator≤q → out q=t q := by
    intro q hq
    have hn : ¬ (h+11≤q ∧ q<separator-1) := by omega
    have hne : q≠h+8 := by omega
    simp [out,fillRange,setAt,hn,hne]
  have hcontrol : ∀ q, h+11≤q → q<separator → out q=true := by
    intro q hq hq'
    by_cases heq : q=separator-1
    · subst q
      have hn : ¬ (h+11≤separator-1 ∧ separator-1<separator-1) := by omega
      have hne : separator-1≠h+8 := by omega
      simpa [out,fillRange,setAt,hn,hne] using marker
    · have hi : h+11≤q ∧ q<separator-1 := by omega
      simp [out,fillRange,hi]
  have hselector : ∃ m : Nat, 0<m ∧
      silentSegment machine (cfg 83 head out) (cfg 93 (h-3) out) m := by
    by_cases hr0 : r=0
    · have hh0 : head=h+7 := by simpa [head,hr0]
      refine ⟨32,by omega,?_⟩
      rw [hh0]
      exact selector_empty h out hpath hleft
    · let q := r-1
      have hrq : r=q+1 := by dsimp [q]; omega
      have hq : (q : Int)=separator-(h+13) := by omega
      have hhq : head=h+10+(q : Int) := by dsimp [head]; rw [if_neg hr0]; omega
      have hrun : ∀ x, h+11≤x → x≤h+10+(q : Int) → out x=true := by
        intro x hx hx'
        have hi : h+11≤x ∧ x<separator-1 := by omega
        simp [out,fillRange,hi]
      refine ⟨q+31,by omega,?_⟩
      rw [hhq]
      exact selector_long h q out hpath hleft h8 h9 h10 hrun
  obtain ⟨m,hm',hsel⟩ := hselector
  have hdispatch := dispatch_zero_next_path h out hpath
  have hone := oneSeg machine _ _ (step64_one (h+8) out h8)
  have hone' : silentSegment machine (cfg 64 (h+8) out) (cfg 280 (h+9) out) 1 := by
    have he' : h+8+1=h+9 := by omega
    simpa only [he'] using hone
  have first := segAdd machine _ _ _ duration m hprep hsel
  have second := segAdd machine _ _ _ (duration+m) 11 first hdispatch
  have all := segAdd machine _ _ _ (duration+m+11) 1 second hone'
  have hpos : 0<duration := by dsimp [duration]; split_ifs <;> omega
  exact ⟨duration+m+11+1,by omega,hpath,hleft,h8,h9,h10,hcontrol,hframe,all⟩

theorem prepare_and_enter (h separator : Int) (t : Int → Bool)
    (hlong : h+12≤separator) (path : Holds t (h-4) zeroNextPath)
    (left : ∀ q, q<h-4 → t q=false)
    (gap : ∀ q, h+5<q → q<separator-1 → t q=false)
    (marker : t (separator-1)=true) :
    let out := fillRange (setAt (h+8) t) (h+11) (separator-1)
    ∃ k : Nat, 0<k ∧ Holds out (h-4) zeroNextPath ∧
      (∀ q, q<h-4 → out q=false) ∧ out (h+8)=true ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 64 (h+8) t) (cfg 280 (h+9) out) k := by
  obtain ⟨k,hk,hpath,hleft,h8,_,_,_,hframe,hseg⟩ :=
    prepare_and_enter_full h separator t hlong path left gap marker
  exact ⟨k,hk,hpath,hleft,h8,hframe,hseg⟩

#print axioms prepare_and_enter_full
#print axioms prepare_and_enter
end Shared.Beeping.NPcoNP.Native64ReturnTo280
