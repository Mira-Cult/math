import Shared.Beeping.NPcoNP.NativeHalfScannerReturns
import Shared.Beeping.NPcoNP.NativeHalfCarryTo93

/-! Compose the physical fill and clear scans with the complete silent
selector return to state 93. The hypotheses describe a supplied boundary;
they do not establish that this boundary is reachable from blank tape. -/
namespace Shared.Beeping.NPcoNP.NativeHalfScannerSelector

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerReturns
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeHalfCarryTo93
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- A nonempty filled run supplies the marker for the selector return. -/
theorem fill_through_selector (k : Nat) (h z a : Int) (t : Int → Bool)
    (xs : List Bool) (hk : 0<k)
    (hz : ∀ i : Nat, i<k → t (h+(i : Int))=false)
    (hm : t (h+(k : Int))=true) (htail : ∀ p ≤ z, t p=false)
    (hx : Holds t a xs)
    (hd : a+(xs.length : Int)≤h ∨ h+(k : Int)≤a) :
    ∃ (n : Nat) (e : Config 284), k+2<n ∧ e.state=93 ∧
      e.tape=fillRange t h (h+(k : Int)) ∧ Holds e.tape a xs ∧
      silentSegment machine (cfg 10 h t) e n := by
  let u := fillRange t h (h+(k : Int))
  have ht : ∀ p ≤ min z (h-1), u p=false := by
    intro p hp
    have hpz : p≤z := le_trans hp (min_le_left _ _)
    have hph : p≤h-1 := le_trans hp (min_le_right _ _)
    have hn : ¬ (h≤p ∧ p<h+(k : Int)) := by omega
    simp [u,fillRange,hn,htail p hpz]
  have hm' : u ((h+(k : Int)-2)+1)=true := by
    have hr : h≤(h+(k : Int)-2)+1 ∧ (h+(k : Int)-2)+1<h+(k : Int) := by omega
    simp [u,fillRange,hr]
  obtain ⟨m,e,hmpos,hstate,htape,hseg⟩ := state83_to_93 (h+(k : Int)-2) (min z (h-1)) u ht hm'
  have hframe := fill_frame t h (h+(k : Int)) a xs hx hd
  refine ⟨k+2+m,e,by omega,hstate,htape,?_,?_⟩
  · rw [htape]; exact hframe
  · exact segAdd machine _ _ _ (k+2) m (scan10_return83 k h t hk hz hm) hseg

/-- A left marker and a zero tail make the clearing return reach state 93.
The complete final tape and any disjoint protected word are preserved. -/
theorem clear_through_selector (k : Nat) (h z a p : Int) (t : Int → Bool)
    (xs : List Bool) (hk : 0<k)
    (ho : ∀ i : Nat, i<k → t (h+(i : Int))=true)
    (hz : t (h+(k : Int))=false) (htail : ∀ q ≤ z, t q=false)
    (hp : p<h) (hmark : t p=true) (hx : Holds t a xs)
    (hd : a+(xs.length : Int)≤h ∨ h+(k : Int)≤a) :
    ∃ (n : Nat) (e : Config 284), k+2<n ∧ e.state=93 ∧
      e.tape=put (clearRange t h (h+(k : Int))) (h+(k : Int)-1) true ∧
      Holds e.tape a xs ∧ silentSegment machine (cfg 28 h t) e n := by
  let u := put (clearRange t h (h+(k : Int))) (h+(k : Int)-1) true
  have ht : ∀ q ≤ min z (h-1), u q=false := by
    intro q hq
    have hqz : q≤z := le_trans hq (min_le_left _ _)
    have hqh : q≤h-1 := le_trans hq (min_le_right _ _)
    have hn : ¬ (h≤q ∧ q<h+(k : Int)) := by omega
    have hq' : q ≠ h+(k : Int)-1 := by omega
    simp [u,put,clearRange,hn,hq',htail q hqz]
  have hmark' : u p=true := by
    have hq' : p ≠ h+(k : Int)-1 := by omega
    simp [u,put,clearRange,hq',hmark,not_le_of_gt hp]
  let d := ((h+(k : Int)-2)-p).toNat
  have hdist : (h+(k : Int)-2)-(d : Int)=p := by
    have hn : 0≤(h+(k : Int)-2)-p := by omega
    have he : (d : Int)=(h+(k : Int)-2)-p := Int.toNat_of_nonneg hn
    omega
  have hm : u ((h+(k : Int)-2)-(d : Int))=true := by rw [hdist]; exact hmark'
  obtain ⟨j,hj,_,hfound,hscan⟩ := scan97_marked d (h+(k : Int)-2) u hm
  obtain ⟨m,e,hmpos,hstate,htape,hseg⟩ :=
    state83_to_93 ((h+(k : Int)-2)-(j : Int)) (min z (h-1)) u ht hfound
  have hframe := (scan28_return97_frame k h a t xs hk ho hz hx hd).2
  refine ⟨k+2+j+m,e,by omega,hstate,htape,?_,?_⟩
  · rw [htape]; exact hframe
  · exact segAdd machine _ _ _ (k+2+j) m
      (segAdd machine _ _ _ (k+2) j (scan28_return97 k h t hk ho hz) hscan) hseg

/-- Apply the fill result to a visit of the actual blank-start run. Finite
support supplies the left zero tail; the right marker and run remain explicit. -/
theorem reachable_fill_through_selector (time k : Nat) (a : Int) (xs : List Bool)
    (hs : (machine.system.run time).state=10) (hk : 0<k)
    (hz : ∀ i : Nat, i<k → (machine.system.run time).tape
      ((machine.system.run time).head+(i : Int))=false)
    (hm : (machine.system.run time).tape
      ((machine.system.run time).head+(k : Int))=true)
    (hx : Holds (machine.system.run time).tape a xs)
    (hd : a+(xs.length : Int)≤(machine.system.run time).head ∨
      (machine.system.run time).head+(k : Int)≤a) :
    ∃ (n : Nat) (e : Config 284), k+2<n ∧ e.state=93 ∧
      e.tape=fillRange (machine.system.run time).tape (machine.system.run time).head
        ((machine.system.run time).head+(k : Int)) ∧ Holds e.tape a xs ∧
      silentSegment machine (machine.system.run time) e n := by
  let c := machine.system.run time
  obtain ⟨z,htail⟩ := run_has_left_zero time
  obtain ⟨n,e,hn,he,ht,hframe,hseg⟩ :=
    fill_through_selector k c.head z a c.tape xs hk hz hm htail hx hd
  have hc : c=cfg 10 c.head c.tape := by
    have he' : c=cfg c.state c.head c.tape := by cases c; rfl
    have hs' : c.state=10 := hs
    simpa only [hs'] using he'
  refine ⟨n,e,hn,he,ht,hframe,?_⟩
  simpa [← hc] using hseg

/-- The corresponding actual-run result for a clear scan; a surviving left
marker remains an explicit hypothesis. -/
theorem reachable_clear_through_selector (time k : Nat) (a p : Int) (xs : List Bool)
    (hs : (machine.system.run time).state=28) (hk : 0<k)
    (ho : ∀ i : Nat, i<k → (machine.system.run time).tape
      ((machine.system.run time).head+(i : Int))=true)
    (hz : (machine.system.run time).tape
      ((machine.system.run time).head+(k : Int))=false)
    (hp : p<(machine.system.run time).head) (hm : (machine.system.run time).tape p=true)
    (hx : Holds (machine.system.run time).tape a xs)
    (hd : a+(xs.length : Int)≤(machine.system.run time).head ∨
      (machine.system.run time).head+(k : Int)≤a) :
    ∃ (n : Nat) (e : Config 284), k+2<n ∧ e.state=93 ∧
      e.tape=put (clearRange (machine.system.run time).tape (machine.system.run time).head
        ((machine.system.run time).head+(k : Int)))
        ((machine.system.run time).head+(k : Int)-1) true ∧ Holds e.tape a xs ∧
      silentSegment machine (machine.system.run time) e n := by
  let c := machine.system.run time
  obtain ⟨z,htail⟩ := run_has_left_zero time
  obtain ⟨n,e,hn,he,ht,hframe,hseg⟩ :=
    clear_through_selector k c.head z a p c.tape xs hk ho hz htail hp hm hx hd
  have hc : c=cfg 28 c.head c.tape := by
    have he' : c=cfg c.state c.head c.tape := by cases c; rfl
    have hs' : c.state=28 := hs
    simpa only [hs'] using he'
  refine ⟨n,e,hn,he,ht,hframe,?_⟩
  simpa [← hc] using hseg

end Shared.Beeping.NPcoNP.NativeHalfScannerSelector

#print axioms Shared.Beeping.NPcoNP.NativeHalfScannerSelector.fill_through_selector
#print axioms Shared.Beeping.NPcoNP.NativeHalfScannerSelector.clear_through_selector
#print axioms Shared.Beeping.NPcoNP.NativeHalfScannerSelector.reachable_fill_through_selector
#print axioms Shared.Beeping.NPcoNP.NativeHalfScannerSelector.reachable_clear_through_selector
