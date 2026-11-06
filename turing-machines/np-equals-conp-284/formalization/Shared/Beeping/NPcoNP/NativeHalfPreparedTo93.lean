import Shared.Beeping.NPcoNP.NativeHalfCarryTo93
import Shared.Beeping.NPcoNP.NativeHalfPreparedReachable
import Shared.Beeping.NPcoNP.NativeHalfState1FiniteSupport

/-! A conditional actual-run consequence: when the blank-start machine visits
the specified exceptional prepared boundary, finite support supplies both
the left-zero tail and the finite carry needed to reach state 93. No theorem
here claims that this boundary is reached or that HALF is complete. -/
namespace Shared.Beeping.NPcoNP.NativeHalfPreparedTo93
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfState1FiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfPreparedReachable
open Shared.Beeping.NPcoNP.NativeHalfCarryTo93

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- If the actual blank-start run reaches the exceptional prepared state-30
boundary, it reaches state 93 in positive finite time without a beep. -/
theorem reachable_exceptional_to_93 (time : Nat) (back : Int → Bool) (gap : Int)
    (left values : List Nat)
    (hconfig : machine.system.run time =
      cfg 30 (gap+1+((leftSuffix left).length : Int))
        (prior (before back gap (leftSuffix left))
          (gap+1+((leftSuffix left).length : Int)) (false :: UnaryBank.encode values))) :
    ∃ (n : Nat) (e : Config 284), 0 < n ∧ e.state=93 ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨z,hz⟩ := run_has_left_zero time
  let z' := min z (gap-1)
  have hleft : ∀ q ≤ z', back q=false := by
    intro q hq
    have hqz : q ≤ z := le_trans hq (min_le_left _ _)
    have hqgap : q < gap := by
      have hh := le_trans hq (min_le_right z (gap-1))
      omega
    have hlen : 0 < ((leftSuffix left).length : Int) := by exact_mod_cast suffix_length_pos left
    have hqb : q < gap+1+((leftSuffix left).length : Int) := by omega
    have ht := hz q hqz
    rw [hconfig] at ht
    change prior (before back gap (leftSuffix left))
      (gap+1+((leftSuffix left).length : Int)) (false :: UnaryBank.encode values) q = false at ht
    rw [prior_left _ _ _ _ hqb, before_prefix _ _ _ _ hqgap] at ht
    exact ht
  let bound := ((gap-1)-min z' (gap-1)).toNat
  have hb : (gap-1)-(bound : Int) ≤ z' := by
    have hnonneg : 0 ≤ (gap-1)-min z' (gap-1) := by omega
    have hh : (bound : Int)=(gap-1)-min z' (gap-1) := Int.toNat_of_nonneg hnonneg
    omega
  have hzero : back ((gap-1)-(bound : Int))=false := hleft _ hb
  obtain ⟨k,_,hcarry⟩ := first_zero bound (gap-1) back hzero
  obtain ⟨n,e,hn,hstate,_,_,hseg⟩ :=
    exceptional_through_93 back gap left values k hcarry z' hleft
  refine ⟨n,e,hn,hstate,?_⟩
  rw [hconfig]
  exact hseg

end Shared.Beeping.NPcoNP.NativeHalfPreparedTo93
