import Shared.Beeping.NPcoNP.NativeRow13Dispatch
import Shared.Beeping.NPcoNP.NativeHalfState10Exact
import Shared.Beeping.NPcoNP.NativeHalfState10Progress
import Shared.Beeping.NPcoNP.NativeHalfScannerReturns

/-! Exact preparation for the row-13 native-half dispatch. -/
namespace Shared.Beeping.NPcoNP.NativeRow13Prepare
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerReturns
open Shared.Beeping.NPcoNP.NativeRow13Dispatch
open Shared.Beeping.NPcoNP.NativeRow12Carry
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

theorem step74_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 74 h t)=(cfg 42 (h+1) (setAt h t),false) := by
  have row : machine.table.row 74 false=⟨true,.right,42,false⟩ := by decide
  have hw : (⟨74,h,t⟩ : Config 284).write true=setAt h t := rfl
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

/-- On a supplied long-gap frame, the row-13 path prepares its control
marker and reaches state 83 in finite silent time, preserving the bank suffix. -/
theorem row13_prepare (h separator : Int) (t : Int → Bool)
    (hlong : h+14≤separator) (path : Holds t (h-4) nextPath)
    (gap : ∀ q, h+7<q → q<separator-1 → t q=false)
    (marker : t (separator-1)=true) :
    let out := fillRange (setAt (h+10) t) (h+12) (separator-1)
    ∃ k : Nat, 0<k ∧ out (h+10)=true ∧
      (∀ q, q<h+10 → out q=t q) ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (h-3) t) (cfg 83 (separator-3) out) k := by
  dsimp only
  let r := (separator-(h+13)).toNat
  have hr : (r : Int)=separator-(h+13) := Int.toNat_of_nonneg (by omega)
  have hp : 0<r := by omega
  have h0 : t (h+10)=false := gap _ (by omega) (by omega)
  have h1 : t (h+11)=false := gap _ (by omega) (by omega)
  have hz : ∀ i : Nat, i<r → (setAt (h+10) t) (h+12+(i : Int))=false := by
    intro i hi
    have hg := gap (h+12+(i : Int)) (by omega) (by omega)
    simpa [setAt,show h+12+(i : Int)≠h+10 by omega] using hg
  have hm : (setAt (h+10) t) (h+12+(r : Int))=true := by
    have he : h+12+(r : Int)=separator-1 := by omega
    rw [he]
    simpa [setAt,show separator-1≠h+10 by omega] using marker
  let u := setAt (h+10) t
  let out := fillRange u (h+12) (separator-1)
  have hu : u (h+11)=false := by simpa [u,setAt] using h1
  have a := oneSeg machine _ _ (step74_zero (h+10) t h0)
  have b := oneSeg machine _ _ (step42_zero (h+11) u hu)
  have a' : silentSegment machine (cfg 74 (h+10) t) (cfg 42 (h+11) u) 1 := by
    simpa only [show h+10+1=h+11 by omega,u] using a
  have ab : silentSegment machine (cfg 74 (h+10) t) (cfg 10 (h+12) u) 2 := by
    have e := segAdd machine _ _ _ 1 1 a' b
    simpa [Int.add_assoc] using e
  have hc := scan10_return83 r (h+12) u hp hz hm
  have he : h+12+(r : Int)=separator-1 := by omega
  have hp' : h+12+(r : Int)-2=separator-3 := by omega
  have hc' : silentSegment machine (cfg 10 (h+12) u) (cfg 83 (separator-3) out) (r+2) := by
    simpa only [he,show separator-1-2=separator-3 by omega,out] using hc
  have hd := dispatch_row13_path h t path
  have hab := segAdd machine _ _ _ 13 2 hd ab
  refine ⟨13+2+(r+2),by omega,?_,?_,?_,segAdd machine _ _ _ (13+2) (r+2) hab hc'⟩
  · simp [out,u,fillRange,setAt]
  · intro q hq
    simp [out,u,fillRange,setAt,show q≠h+10 by omega,show ¬ (h+12≤q ∧ q<separator-1) by omega]
  · intro q hq
    simp [out,u,fillRange,setAt,show q≠h+10 by omega,show ¬ (h+12≤q ∧ q<separator-1) by omega]

#print axioms step74_zero
#print axioms row13_prepare
end Shared.Beeping.NPcoNP.NativeRow13Prepare
