import Shared.Beeping.NPcoNP.Native51Prepare
import Shared.Beeping.NPcoNP.Native54Prepare

/-! Literal state-64 zero preparation, including an empty control gap. -/
namespace Shared.Beeping.NPcoNP.Native64Prepare
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.Native51Prepare
open Shared.Beeping.NPcoNP.Native54Prepare
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem step64_zero (x : Int) (t : Int → Bool) (ht : t x=false) :
    machine.step (cfg 64 x t)=(cfg 9 (x+1) (setAt x t),false) := by
  have row : machine.table.row 64 false=⟨true,.right,9,false⟩ := by decide
  have hw : (⟨64,x,t⟩ : Config 284).write true=setAt x t := rfl
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

/-- State 64 shares state 51's zero preparation, but its positive branch is
separate. This theorem covers both empty and nonempty zero gaps. -/
theorem zero_prepare_to83_exact (x : Int) (t : Int → Bool) (k : Nat)
    (h0 : t x=false) (h1 : t (x+1)=false) (h2 : t (x+2)=false)
    (zeros : ∀ i : Nat, i<k → t (x+3+(i : Int))=false)
    (marker : t (x+3+(k : Int))=true) :
    let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
    let head := if k=0 then x-1 else x+3+(k : Int)-2
    let duration := if k=0 then 7 else k+5
    silentSegment machine (cfg 64 x t) (cfg 83 head out) duration := by
  dsimp only
  let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
  let head := if k=0 then x-1 else x+3+(k : Int)-2
  let duration := if k=0 then 7 else k+5
  have hp : 0<duration := by dsimp [duration]; split_ifs <;> omega
  have hd : duration-1+1=duration := by omega
  have he : machine.step (cfg 51 x t)=machine.step (cfg 64 x t) := by
    rw [step51_zero x t h0,step64_zero x t h0]
  have hs : silentSegment machine (cfg 51 x t) (cfg 83 head out) (duration-1+1) := by
    rw [hd]
    exact Native51Prepare.zero_prepare_to83_exact x t k h0 h1 h2 zeros marker
  have hr := (replace_equal_first machine (cfg 51 x t) (cfg 64 x t)
    (cfg 83 head out) (duration-1) he).mp hs
  simpa only [hd,out,head,duration] using hr

/-- A supplied state-64 control gap prepares silently and leaves every
cell at or beyond the separator untouched. -/
theorem prepare_from_gap (h separator : Int) (t : Int → Bool)
    (hlong : h+12≤separator)
    (gap : ∀ q, h+5<q → q<separator-1 → t q=false)
    (marker : t (separator-1)=true) :
    let out := fillRange (setAt (h+8) t) (h+11) (separator-1)
    ∃ (k : Nat) (head : Int), 0<k ∧ out (h+8)=true ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 64 (h+8) t) (cfg 83 head out) k := by
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
  have hs := zero_prepare_to83_exact (h+8) t r h0 h1 h2 hz hm
  let out := fillRange (setAt (h+8) t) (h+11) (separator-1)
  let duration := if r=0 then 7 else r+5
  let head := if r=0 then h+7 else separator-3
  have he : h+11+(r : Int)=separator-1 := by omega
  have hh : (if r=0 then h+8-1 else h+8+3+(r : Int)-2)=head := by
    dsimp [head]
    split_ifs <;> omega
  have hh' : (if r=0 then h+8-1 else separator-1-2)=head := by
    dsimp [head]
    split_ifs <;> omega
  have hs' : silentSegment machine (cfg 64 (h+8) t) (cfg 83 head out) duration := by
    simpa only [show h+8+3=h+11 by omega,he,hh,hh',out,duration] using hs
  have hmark : out (h+8)=true := by simp [out,fillRange,setAt]
  have hframe : ∀ q, separator≤q → out q=t q := by
    intro q hq
    have hn : ¬ (h+11≤q ∧ q<separator-1) := by omega
    have hne : q≠h+8 := by omega
    simp [out,fillRange,setAt,hn,hne]
  exact ⟨duration,head,by dsimp [duration]; split_ifs <;> omega,hmark,hframe,hs'⟩

#print axioms step64_zero
#print axioms zero_prepare_to83_exact
#print axioms prepare_from_gap
end Shared.Beeping.NPcoNP.Native64Prepare
