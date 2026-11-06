import Shared.Beeping.NPcoNP.NativeHalfScannerSelector
import Shared.Beeping.NPcoNP.NativeHalfState10Progress

/-! A complete state-261 zero-dispatch, exact run fill, and selector return.
The prepared tape hypotheses are explicit and no graph invariant is assumed. -/
namespace Shared.Beeping.NPcoNP.NativeHalfDispatchSelector

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfScannerSelector

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Starting at 261, the two paid dispatch steps and nonempty zero fill
complete the selector return, preserving any word outside the entire region
that may be written. -/
theorem dispatch_zero_through_selector (k : Nat) (h z a : Int)
    (t : Int → Bool) (xs : List Bool) (hk : 0<k)
    (h0 : t h=false) (h1 : t (h+1)=false)
    (hz : ∀ i : Nat, i<k → t (h+2+(i : Int))=false)
    (hm : t (h+2+(k : Int))=true) (htail : ∀ p ≤ z, t p=false)
    (hx : Holds t a xs)
    (hd : a+(xs.length : Int)≤h ∨ h+2+(k : Int)≤a) :
    ∃ (n : Nat) (e : Config 284), k+4<n ∧ e.state=93 ∧
      e.tape=fillRange (setAt h t) (h+2) (h+2+(k : Int)) ∧
      Holds e.tape a xs ∧ silentSegment machine (cfg 261 h t) e n := by
  let u := setAt h t
  have h1' : u (h+1)=false := by simp [u,setAt,h1]
  have hz' : ∀ i : Nat, i<k → u (h+2+(i : Int))=false := by
    intro i hi
    have hp : h+2+(i : Int) ≠ h := by omega
    simp [u,setAt,hp,hz i hi]
  have hm' : u (h+2+(k : Int))=true := by
    have hp : h+2+(k : Int) ≠ h := by omega
    simp [u,setAt,hp,hm]
  have htail' : ∀ p ≤ min z (h-1), u p=false := by
    intro p hp
    have hpz : p≤z := le_trans hp (min_le_left _ _)
    have hph : p≤h-1 := le_trans hp (min_le_right _ _)
    have hp' : p≠h := by omega
    simp [u,setAt,hp',htail p hpz]
  have hx' : Holds u a xs := by
    apply holds_transport t u a xs hx
    intro p hlo hhi
    have hp : p≠h := by omega
    simp [u,setAt,hp]
  have hd' : a+(xs.length : Int)≤h+2 ∨ h+2+(k : Int)≤a := by omega
  obtain ⟨n,e,hn,he,ht,hframe,hseg⟩ :=
    fill_through_selector k (h+2) (min z (h-1)) a u xs hk hz' hm' htail' hx' hd'
  have hfirst := oneSeg machine _ _ (step261_zero h t h0)
  have hsecond := oneSeg machine _ _ (step42_zero (h+1) u h1')
  have hdispatch : silentSegment machine (cfg 261 h t) (cfg 10 (h+2) u) 2 := by
    simpa [u,Int.add_assoc] using segAdd machine _ _ _ 1 1 hfirst hsecond
  refine ⟨2+n,e,by omega,he,ht,hframe,?_⟩
  exact segAdd machine _ _ _ 2 n hdispatch hseg

end Shared.Beeping.NPcoNP.NativeHalfDispatchSelector

#print axioms Shared.Beeping.NPcoNP.NativeHalfDispatchSelector.dispatch_zero_through_selector
