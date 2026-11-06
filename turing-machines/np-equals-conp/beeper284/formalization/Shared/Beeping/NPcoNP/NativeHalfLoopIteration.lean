import Shared.Beeping.NPcoNP.NativeHalfRegularIteration
import Shared.Beeping.NPcoNP.NativeHalfLoopLayout
import Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic

/-! Finite iteration of literal prepared regular HALF cycles. The final
state and tape are exposed for the separately proved cleanup routines. This
does not establish that blank start reaches the supplied configuration. -/
namespace Shared.Beeping.NPcoNP.NativeHalfLoopIteration
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfRegularIteration
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.NativeHalfLoopLayout
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def bases (base : Int → Bool) (b : Int) : Nat → Int → Bool
  | 0 => base
  | i+1 => put (bases base b i) (boundary b (i+1)) true

def value (m i : Nat) : Nat := m - 3 - 2*i

def tailValues (xs : List Nat) (i : Nat) : List Nat := xs ++ List.replicate i 0

theorem bases_bit (base : Int → Bool) (b : Int) (hb : base b = true) (i : Nat) :
    bases base b i (boundary b i) = true := by
  cases i with
  | zero => simpa [bases, boundary] using hb
  | succ i => simp [bases, put]

theorem value_next (m i k : Nat) (hi : i < k) (hk : 2*k + 3 ≤ m) :
    value m i = value m (i+1) + 2 := by
  simp only [value]
  omega

theorem tail_next (xs : List Nat) (i : Nat) :
    tailValues xs (i+1) = tailValues xs i ++ [0] := by
  simp [tailValues, List.replicate_succ', List.append_assoc]

theorem layout_link (base : Int → Bool) (b : Int) (m k : Nat) (xs : List Nat)
    (hk : 2*k + 3 ≤ m) (i : Nat) (hi : i < k) :
    after (bases base b i) (boundary b i + 1)
        (suffix (value m) (tailValues xs) i) =
      prior (bases base b (i+1)) (boundary b (i+1))
        (suffix (value m) (tailValues xs) (i+1)) := by
  have hp := next_cycle_layout (bases base b i) (boundary b i)
    (value m (i+1)) (tailValues xs i)
  rw [← value_next m i k hi hk, ← tail_next xs i] at hp
  simpa [bases, boundary, suffix, Int.add_assoc] using hp

/-- Starting at a prepared boundary with `m` ones on its right, perform
`k+1` regular cycles whenever the last one is admissible. The exact final
tape and total duration are explicit, and every step is silent. -/
theorem prepared_iterations (base : Int → Bool) (b : Int) (m k : Nat)
    (xs : List Nat) (hb : base b = true) (hk : 2*k + 3 ≤ m) :
    silentSegment machine
      (cfg 30 (boundary b 0)
        (prior (bases base b 0) (boundary b 0) (suffix (value m) (tailValues xs) 0)))
      (cfg 30 (boundary b k + 1)
        (after (bases base b k) (boundary b k + 1) (suffix (value m) (tailValues xs) k)))
      (totalDuration (value m) (tailValues xs) k + duration (value m) (tailValues xs) k) :=
  regular_chain_with_last (bases base b) b (value m) (tailValues xs) k
    (fun i _ => bases_bit base b hb i) (layout_link base b m k xs hk)

theorem prepared_iterations_positive (m k : Nat) (xs : List Nat) :
    0 < totalDuration (value m) (tailValues xs) k + duration (value m) (tailValues xs) k := by
  simp only [duration]
  omega

/-- The arithmetic quantity retained after the given number of cycles. -/
theorem prepared_iterations_arithmetic (a m k : Nat) (ha : 1 ≤ a)
    (hk : 2*k + 3 ≤ m) :
    sourceValue (a + (k+1)) (m - 2*(k+1)) = sourceValue a m := by
  apply iteration_preserves a m (k+1) ha
  omega

end Shared.Beeping.NPcoNP.NativeHalfLoopIteration
