import Shared.Beeping.NPcoNP.NativeTerminalMarkerReturn

/-! Geometric facts about the marker-at-head fill used by later operations. -/
namespace Shared.Beeping.NPcoNP.NativeTerminalMarkerGeometry
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Every cell in the filled corridor is marked, and the left blank ray is
preserved across the update. -/
theorem terminal_fill_full_geometry (t : Int → Bool) (a : Int) (r : Nat)
    (blank : ∀ q, q<a-2 → t q=false) (left0 : t (a-2)=false)
    (zero : t (a+5)=false) :
    let out := fillRange (setAt (a+3) t) (a+6) (a+6+(r : Int))
    (∀ q, q<a-1 → out q=false) ∧ out (a+5)=false ∧
      (∀ q, a+6≤q → q<a+6+(r : Int) → out q=true) := by
  dsimp only
  let out := fillRange (setAt (a+3) t) (a+6) (a+6+(r : Int))
  have frame : ∀ q, q<a+6 → q≠a+3 → out q=t q := by
    intro q hq hne
    simp [out,fillRange,setAt,show ¬a+6≤q by omega,hne]
  refine ⟨?_,?_,?_⟩
  · intro q hq
    have ht : t q=false := by
      by_cases he : q=a-2
      · simpa only [he] using left0
      · exact blank q (by omega)
    exact (frame q (by omega) (by omega)).trans ht
  · exact (frame _ (by omega) (by omega)).trans zero
  · intro q hq hq'
    simp [out,fillRange,show a+6≤q ∧ q<a+6+(r : Int) by omega]

/-- The filled corridor supplies the four marked cells and the blank ray
needed by the next zero branch. -/
theorem terminal_fill_geometry (t : Int → Bool) (a : Int) (r : Nat) (hr : 4≤r)
    (blank : ∀ q, q<a-2 → t q=false) (left0 : t (a-2)=false)
    (zero : t (a+5)=false) :
    let out := fillRange (setAt (a+3) t) (a+6) (a+6+(r : Int))
    (∀ q, q<a-1 → out q=false) ∧ out (a+5)=false ∧
      (∀ q, a+6≤q → q≤a+9 → out q=true) := by
  have h := terminal_fill_full_geometry t a r blank left0 zero
  dsimp only at h ⊢
  exact ⟨h.1,h.2.1,by intro q hq hq'; exact h.2.2 q hq (by omega)⟩

#print axioms terminal_fill_geometry
end Shared.Beeping.NPcoNP.NativeTerminalMarkerGeometry
