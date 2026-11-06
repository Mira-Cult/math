import Shared.Beeping.NPcoNP.NativeHalfScannerFrames
import Shared.Beeping.NPcoNP.NativeHalfState28Exit
import Shared.Beeping.NPcoNP.NativeHalfState97Progress

/-! Exact scan-and-return segments for the literal table. Both the complete
tape effect and disjoint finite-word frames are retained. -/
namespace Shared.Beeping.NPcoNP.NativeHalfScannerReturns

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState28Exit
open Shared.Beeping.NPcoNP.NativeHalfState97Progress

/-- A nonempty zero run is filled by state 10, then state 97 reads the last
filled cell and returns to state 83 in one more silent transition. -/
theorem scan10_return83 (k : Nat) (h : Int) (t : Int → Bool)
    (hk : 0<k) (hz : ∀ i : Nat, i<k → t (h+(i : Int))=false)
    (hm : t (h+(k : Int))=true) :
    silentSegment machine (cfg 10 h t)
      (cfg 83 (h+(k : Int)-2) (fillRange t h (h+(k : Int)))) (k+2) := by
  have hpos : h≤h+(k : Int)-1 ∧ h+(k : Int)-1<h+(k : Int) := by omega
  have hmark : fillRange t h (h+(k : Int)) (h+(k : Int)-1)=true := by
    simp [fillRange,hpos]
  have hscan := scan10_exact k h t hz hm
  have hstep := oneSeg machine _ _ (step97_one (h+(k : Int)-1)
    (fillRange t h (h+(k : Int))) hmark)
  have hall := segAdd machine _ _ _ (k+1) 1 hscan hstep
  simpa [Int.sub_sub, Nat.add_assoc] using hall

/-- A nonempty one run is cleared by state 28, then state 6 restores the
last cleared cell and enters state 97 in one more silent transition. -/
theorem scan28_return97 (k : Nat) (h : Int) (t : Int → Bool)
    (hk : 0<k) (ho : ∀ i : Nat, i<k → t (h+(i : Int))=true)
    (hz : t (h+(k : Int))=false) :
    silentSegment machine (cfg 28 h t)
      (cfg 97 (h+(k : Int)-2)
        (put (clearRange t h (h+(k : Int))) (h+(k : Int)-1) true)) (k+2) := by
  have hpos : h≤h+(k : Int)-1 ∧ h+(k : Int)-1<h+(k : Int) := by omega
  have hzero : clearRange t h (h+(k : Int)) (h+(k : Int)-1)=false := by
    simp [clearRange,hpos]
  have hscan := scan28_exact k h t ho hz
  have hstep := oneSeg machine _ _ (step6_zero (h+(k : Int)-1)
    (clearRange t h (h+(k : Int))) hzero)
  have hall := segAdd machine _ _ _ (k+1) 1 hscan hstep
  simpa [Int.sub_sub, Nat.add_assoc] using hall

/-- The state-10 return leaves any disjoint protected word intact. -/
theorem scan10_return83_frame (k : Nat) (h a : Int) (t : Int → Bool) (xs : List Bool)
    (hk : 0<k) (hz : ∀ i : Nat, i<k → t (h+(i : Int))=false)
    (hm : t (h+(k : Int))=true) (hx : Holds t a xs)
    (hd : a+(xs.length : Int)≤h ∨ h+(k : Int)≤a) :
    silentSegment machine (cfg 10 h t)
        (cfg 83 (h+(k : Int)-2) (fillRange t h (h+(k : Int)))) (k+2) ∧
      Holds (fillRange t h (h+(k : Int))) a xs :=
  ⟨scan10_return83 k h t hk hz hm,fill_frame t h (h+(k : Int)) a xs hx hd⟩

/-- The state-28 return also preserves any word outside its written run. -/
theorem scan28_return97_frame (k : Nat) (h a : Int) (t : Int → Bool) (xs : List Bool)
    (hk : 0<k) (ho : ∀ i : Nat, i<k → t (h+(i : Int))=true)
    (hz : t (h+(k : Int))=false) (hx : Holds t a xs)
    (hd : a+(xs.length : Int)≤h ∨ h+(k : Int)≤a) :
    silentSegment machine (cfg 28 h t)
        (cfg 97 (h+(k : Int)-2)
          (put (clearRange t h (h+(k : Int))) (h+(k : Int)-1) true)) (k+2) ∧
      Holds (put (clearRange t h (h+(k : Int))) (h+(k : Int)-1) true) a xs := by
  refine ⟨scan28_return97 k h t hk ho hz,?_⟩
  have hframe := clear_frame t h (h+(k : Int)) a xs hx hd
  apply holds_transport (clearRange t h (h+(k : Int))) _ a xs hframe
  intro p hlo hhi
  have hp : p ≠ h+(k : Int)-1 := by omega
  rw [put_other _ _ _ _ hp]

end Shared.Beeping.NPcoNP.NativeHalfScannerReturns

#print axioms Shared.Beeping.NPcoNP.NativeHalfScannerReturns.scan10_return83_frame
#print axioms Shared.Beeping.NPcoNP.NativeHalfScannerReturns.scan28_return97_frame
