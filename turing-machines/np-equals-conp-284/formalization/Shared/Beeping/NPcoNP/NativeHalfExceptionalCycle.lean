import Shared.Beeping.NPcoNP.NativeHalfCyclePrelude
import Shared.Beeping.NPcoNP.NativeHalfCycleTape
import Shared.Beeping.NPcoNP.NativeHalfZeroPrefixReturn

/-! A prepared native-HALF boundary with exactly two remaining ones. The
literal table takes the zero-prefixed suffix path to the old decrement
scanner. This local segment does not establish reachability, cleanup,
the return-selector ABI, or correctness of the complete HALF routine. -/
namespace Shared.Beeping.NPcoNP.NativeHalfExceptionalCycle

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The selected boundary has two ones followed by its zero delimiter and
an encoded bank. The three-row prelude followed by the zero-prefixed suffix
shift reaches state 18 with its exact whole-tape postcondition. -/
theorem exceptional_cycle (base : Int → Bool) (b : Int) (values : List Nat)
    (hb : base b = true) :
    let suffix := false :: UnaryBank.encode values
    silentSegment machine
      (cfg 30 b (prior base b suffix))
      (cfg 18 (b+2) (after base (b+1) suffix))
      (2 * suffix.length + 6) := by
  dsimp only
  let suffix := false :: UnaryBank.encode values
  have hp := NativeHalfCyclePrelude.prelude b (prior base b suffix)
    (prior_boundary base b suffix) (prior_first base b suffix) (prior_second base b suffix)
  rw [three_writes base b suffix hb] at hp
  have hs := selected_zero_prefix_shift_return base (b+1) values
  have h := segAdd machine _ _ _ 3 (2*suffix.length+3) hp (by
    simpa [suffix, Int.add_assoc] using hs)
  have htime : 3 + (2*suffix.length+3) = 2*suffix.length+6 := by omega
  rw [htime] at h
  exact h

theorem duration_positive (values : List Nat) :
    0 < 2 * (false :: UnaryBank.encode values).length + 6 := by omega

theorem exceptional_cycle_no_beep (base : Int → Bool) (b : Int) (values : List Nat)
    (hb : base b = true) (j : Nat)
    (hj : j < 2 * (false :: UnaryBank.encode values).length + 6) :
    ¬ machine.system.BeepFrom
      (cfg 30 b (prior base b (false :: UnaryBank.encode values))) j :=
  silent_no_beep machine _ _ _ j (exceptional_cycle base b values hb) hj

end Shared.Beeping.NPcoNP.NativeHalfExceptionalCycle
