import Shared.Beeping.NPcoNP.NativeHalfExceptionalCycle
import Shared.Beeping.NPcoNP.NativeHalfCleanupScan

/-! The exceptional two-one boundary through the forward scan of the
inherited decrement routine. This is a prepared local segment only: the
state-20 reverse rewrite, selector, and blank-start reachability remain open. -/
namespace Shared.Beeping.NPcoNP.NativeHalfExceptionalScan
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfExceptionalCycle
open Shared.Beeping.NPcoNP.NativeHalfCleanupScan
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.UnarySuffixShift

/-- Exact duration of the composed exceptional cycle and cleanup scan. -/
def duration (values : List Nat) : Nat :=
  2 * (false :: UnaryBank.encode values).length + 6 +
    ((false :: UnaryBank.encode values) ++ [true]).length + 2

theorem duration_positive (values : List Nat) : 0 < duration values := by
  simp only [duration]
  omega

/-- The supplied two-one boundary reaches the state-20 reverse rewrite,
with the whole post-shift tape and an empty event word. -/
theorem exceptional_through_scan (base : Int → Bool) (b : Int) (values : List Nat)
    (hb : base b = true) :
    let suffix := false :: UnaryBank.encode values
    let pre := suffix ++ [true]
    silentSegment machine
      (cfg 30 b (prior base b suffix))
      (cfg 20 (b+2+pre.length) (after base (b+1) suffix))
      (duration values) := by
  dsimp only
  have hc := exceptional_cycle base b values hb
  have hs := scan_after_zero_prefix base (b+1) values
  have hs' : silentSegment machine
      (cfg 18 (b+2) (after base (b+1) (false :: UnaryBank.encode values)))
      (cfg 20 (b+2+((false :: UnaryBank.encode values) ++ [true]).length)
        (after base (b+1) (false :: UnaryBank.encode values)))
      (((false :: UnaryBank.encode values) ++ [true]).length+2) := by
    simpa [Int.add_assoc] using hs
  have h := segAdd machine _ _ _
    (2 * (false :: UnaryBank.encode values).length + 6)
    (((false :: UnaryBank.encode values) ++ [true]).length+2) hc hs'
  simpa [duration, Nat.add_assoc] using h

theorem exceptional_through_scan_no_beep (base : Int → Bool) (b : Int)
    (values : List Nat) (hb : base b = true) (j : Nat) (hj : j < duration values) :
    ¬ machine.system.BeepFrom
      (cfg 30 b (prior base b (false :: UnaryBank.encode values))) j :=
  silent_no_beep machine _ _ _ j (exceptional_through_scan base b values hb) hj

end Shared.Beeping.NPcoNP.NativeHalfExceptionalScan
