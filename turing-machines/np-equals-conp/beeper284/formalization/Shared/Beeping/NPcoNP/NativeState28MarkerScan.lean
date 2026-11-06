import Shared.Beeping.NPcoNP.NativeHalfState28Exit
import Shared.Beeping.NPcoNP.NativeHalfState97Progress

namespace Shared.Beeping.NPcoNP.NativeState28MarkerScan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exit
open Shared.Beeping.NPcoNP.NativeHalfState97Progress
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- State 28 preserves a marker strictly left of its initially cleared cell.
The resulting state 6 is still strictly right of that marker. -/
theorem scan_to_zero_with_marker (k : Nat) (h p : Int) (t : Int → Bool)
    (hleft : t (h-1)=false) (hz : t (h+(k : Int))=false)
    (hp : p<h-1) (hmark : t p=true) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ n≤k+1 ∧ e.state=6 ∧
      e.tape e.head=false ∧ p<e.head ∧ e.tape p=true ∧
      silentSegment machine (cfg 28 h t) e n := by
  induction k generalizing h t with
  | zero =>
    refine ⟨1,cfg 6 (h-1) t,by omega,by omega,rfl,hleft,by simpa [cfg] using hp,hmark,?_⟩
    exact oneSeg machine _ _ (step28_zero h t (by simpa using hz))
  | succ k ih =>
    cases hv : t h with
    | false =>
      refine ⟨1,cfg 6 (h-1) t,by omega,by omega,rfl,hleft,by simpa [cfg] using hp,hmark,?_⟩
      exact oneSeg machine _ _ (step28_zero h t hv)
    | true =>
      have hneq : h+1+(k : Int) ≠ h := by omega
      have hz' : put t h false ((h+1)+(k : Int)) = false := by
        have he : h+1+(k:Int) = h+((Nat.succ k:Nat):Int) := by push_cast; omega
        rw [put_other _ _ _ _ hneq, he]
        exact hz
      have hleft' : put t h false ((h+1)-1) = false := by simp [put]
      have hmark' : put t h false p=true := by
        rw [put_other _ _ _ _ (by omega)]
        exact hmark
      obtain ⟨n,e,hn,hb,he,ht,hpos,hm,hs⟩ :=
        ih (h+1) (put t h false) hleft' hz' (by omega) hmark'
      refine ⟨1+n,e,by omega,by omega,he,ht,hpos,hm,?_⟩
      exact segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step28_one h t hv)) hs

#print axioms scan_to_zero_with_marker
end Shared.Beeping.NPcoNP.NativeState28MarkerScan
