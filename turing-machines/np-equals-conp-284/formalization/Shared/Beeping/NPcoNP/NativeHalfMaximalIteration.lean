import Shared.Beeping.NPcoNP.NativeHalfLoopIteration

/-! The full finite run of regular HALF cycles from a supplied prepared
boundary. Residual cleanup, selector dispatch, and blank-start reachability
are separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeHalfMaximalIteration
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfRegularIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.UnarySuffixShift

/-- All regular cycles are completed in a finite positive silent segment.
The selected count `(m-1)/2` leaves at most two units for cleanup. -/
theorem maximal_iterations (base : Int → Bool) (b : Int) (m : Nat)
    (xs : List Nat) (hb : base b = true) (hm : 3 ≤ m) :
    let k := regularCount m - 1
    silentSegment machine
      (cfg 30 (boundary b 0)
        (prior (bases base b 0) (boundary b 0) (suffix (value m) (tailValues xs) 0)))
      (cfg 30 (boundary b k + 1)
        (after (bases base b k) (boundary b k + 1) (suffix (value m) (tailValues xs) k)))
      (totalDuration (value m) (tailValues xs) k + duration (value m) (tailValues xs) k) := by
  dsimp only
  have hpos : 0 < regularCount m := (count_positive_iff m).2 hm
  have hlt : regularCount m - 1 < regularCount m := by omega
  have hk := iteration_admissible m _ hlt
  exact prepared_iterations base b m (regularCount m - 1) xs hb hk

theorem maximal_duration_positive (m : Nat) (xs : List Nat) :
    0 < totalDuration (value m) (tailValues xs) (regularCount m - 1) +
      duration (value m) (tailValues xs) (regularCount m - 1) :=
  prepared_iterations_positive m _ xs

/-- Arithmetic residual classification is independent of the still-unproved
physical cleanup. -/
theorem maximal_residual (a m : Nat) (ha : 1 ≤ a) :
    m - 2 * regularCount m ≤ 2 ∧
    sourceValue (a + regularCount m) (m - 2 * regularCount m) = sourceValue a m :=
  ⟨terminal_at_most_two m, terminal_preserves a m ha⟩

end Shared.Beeping.NPcoNP.NativeHalfMaximalIteration
