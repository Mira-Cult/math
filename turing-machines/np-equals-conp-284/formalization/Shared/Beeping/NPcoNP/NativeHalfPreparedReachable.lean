import Shared.Beeping.NPcoNP.NativeHalfExceptionalMarkerProgress
import Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport

/-! Blank-start consequence of the prepared exceptional-HALF result. If the
actual run has the specified prepared configuration, its finite tape support
supplies the protected base's left-zero tail. No reachability of that
configuration or correctness after state 28 is asserted. -/

namespace Shared.Beeping.NPcoNP.NativeHalfPreparedReachable

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfExceptionalMarkerProgress

/-- Preparing the boundary does not alter the base strictly to its left. -/
theorem prior_left (base : Int → Bool) (b q : Int) (suffix : List Bool)
    (hq : q < b) : prior base b suffix q = base q := by
  have h0 : q ≠ b := by omega
  have h1 : q ≠ b + 1 := by omega
  have h2 : q ≠ b + 2 := by omega
  have h3 : q < b + 1 := by omega
  simp [prior, put, before, h0, h1, h2, h3]

/-- Whenever the actual blank-start run has the exceptional prepared
configuration, it proceeds to state 28 in positive finite silent time. -/
theorem reachable_exceptional_to_28 (time : Nat) (base : Int → Bool)
    (b : Int) (values : List Nat) (hb : base b = true)
    (hconfig : machine.system.run time =
      cfg 30 b (prior base b (false :: UnaryBank.encode values))) :
    ∃ (duration : Nat) (e : Config 284), 0 < duration ∧ e.state = 28 ∧
      silentSegment machine (machine.system.run time) e duration := by
  obtain ⟨z, hz⟩ := run_has_left_zero time
  have hleft : ∃ z : Int, ∀ q ≤ z, base q = false := by
    refine ⟨min z (b-1), ?_⟩
    intro q hq
    have hqz : q ≤ z := le_trans hq (min_le_left _ _)
    have hqb : q < b := by
      have h := le_trans hq (min_le_right z (b-1))
      omega
    have hzero := hz q hqz
    rw [hconfig] at hzero
    change prior base b (false :: UnaryBank.encode values) q = false at hzero
    rw [prior_left base b q _ hqb] at hzero
    exact hzero
  obtain ⟨duration, e, hd, he, hs⟩ := exceptional_to_28 base b values hb hleft
  exact ⟨duration, e, hd, he, by rw [hconfig]; exact hs⟩

end Shared.Beeping.NPcoNP.NativeHalfPreparedReachable
