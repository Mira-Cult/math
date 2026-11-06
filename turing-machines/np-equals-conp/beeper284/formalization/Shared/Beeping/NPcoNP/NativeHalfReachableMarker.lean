import Shared.Beeping.NPcoNP.NativeHalfMarkerRetain
import Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport

/-! The actual blank-start machine can apply the marker-preserving scanner
theorem whenever a rightward marker is known at a state-23 boundary. The
marker remains an explicit hypothesis: finite support alone is insufficient.
No state-23 reachability or global tape invariant is asserted. -/

namespace Shared.Beeping.NPcoNP.NativeHalfReachableMarker

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfMarkerRetain
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport

/-- If a blank-start run reaches state 23 with a one at or to the right of
its head, it reaches state 28 through a positive finite silent segment. -/
theorem reachable_marker_to_28 (time : Nat)
    (hstate : (machine.system.run time).state = 23)
    (p : Int) (hpos : (machine.system.run time).head ≤ p)
    (hone : (machine.system.run time).tape p = true) :
    ∃ (duration : Nat) (e : Config 284), 0 < duration ∧ e.state = 28 ∧
      silentSegment machine (machine.system.run time) e duration := by
  let c := machine.system.run time
  obtain ⟨z, hz⟩ := run_has_left_zero time
  let k := (c.head - min z c.head).toNat
  have hk : c.head - (k : Int) ≤ z := by
    have hn : 0 ≤ c.head - min z c.head := by omega
    have he : (k : Int) = c.head - min z c.head := Int.toNat_of_nonneg hn
    omega
  have hleft : ∀ q ≤ c.head - (k : Int), c.tape q = false := by
    intro q hq
    exact hz q (le_trans hq hk)
  obtain ⟨duration, e, hp, he, hs⟩ :=
    marker_to_28 k c.head p c.tape hleft hpos hone
  refine ⟨duration, e, hp, he, ?_⟩
  have hsc : c.state = 23 := hstate
  have hc : c = cfg 23 c.head c.tape := by
    have heta : c = cfg c.state c.head c.tape := by cases c; rfl
    simpa only [hsc] using heta
  simpa [← hc] using hs

end Shared.Beeping.NPcoNP.NativeHalfReachableMarker
