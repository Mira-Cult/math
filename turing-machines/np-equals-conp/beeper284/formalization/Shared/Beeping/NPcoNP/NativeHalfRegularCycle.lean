import Shared.Beeping.NPcoNP.NativeHalfCyclePrelude
import Shared.Beeping.NPcoNP.NativeHalfCycleTape
import Shared.Beeping.NPcoNP.NativeHalfCycleReturn

/-! A single prepared, regular native-HALF cycle of the literal 284-state
table.  The first residual bank has size `x+1`, so the original source block
has size `x+3 > 2`.  The supplied tape and boundary are hypotheses: this
does not establish reachability from blank tape, the exceptional size-two
case, the selector ABI, or correctness of the complete HALF routine. -/
namespace Shared.Beeping.NPcoNP.NativeHalfRegularCycle

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.NativeHalfCycleTape

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Starting at the prepared zero boundary, the literal machine consumes
two ones, shifts the nonempty encoded suffix, and returns to state 30 at the
new boundary. Every one of the stated transitions is silent. -/
theorem regular_cycle (base : Int → Bool) (b : Int) (x : Nat) (xs : List Nat)
    (hb : base b = true) :
    let suffix := UnaryBank.encode (x :: xs)
    silentSegment machine
      (cfg 30 b (prior base b suffix))
      (cfg 30 (b+1) (after base (b+1) suffix))
      (2 * suffix.length + 7) := by
  dsimp only
  let suffix := UnaryBank.encode (x :: xs)
  have hp := NativeHalfCyclePrelude.prelude b (prior base b suffix)
    (prior_boundary base b suffix) (prior_first base b suffix) (prior_second base b suffix)
  rw [three_writes base b suffix hb] at hp
  have hs := NativeHalfCycleReturn.suffix_shift_and_return base (b+1) x xs
  have hread : base (b+1-1) = true := by simpa using hb
  rw [hread] at hs
  simp only [↓reduceIte] at hs
  have h := segAdd machine _ _ _ 3 (2*suffix.length+4) hp (by
    simpa [Int.add_assoc] using hs)
  have htime : 3 + (2*suffix.length+4) = 2*suffix.length+7 := by omega
  rw [htime] at h
  exact h

theorem duration_positive (x : Nat) (xs : List Nat) :
    0 < 2 * (UnaryBank.encode (x :: xs)).length + 7 := by omega

theorem regular_cycle_no_beep (base : Int → Bool) (b : Int) (x : Nat)
    (xs : List Nat) (hb : base b = true) (j : Nat)
    (hj : j < 2 * (UnaryBank.encode (x :: xs)).length + 7) :
    ¬ machine.system.BeepFrom (cfg 30 b (prior base b (UnaryBank.encode (x :: xs)))) j :=
  silent_no_beep machine _ _ _ j (regular_cycle base b x xs hb) hj

end Shared.Beeping.NPcoNP.NativeHalfRegularCycle
