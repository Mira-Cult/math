import Shared.Beeping.NPcoNP.NativeHalfRegularCycle

/-! Finite concatenation of the literal table's prepared regular cycles.
The caller supplies the representation of each successive prepared tape;
this interface does not by itself prove the source bank layout or HALf's
cleanup and return behavior. -/
namespace Shared.Beeping.NPcoNP.NativeHalfRegularIteration
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfRegularCycle
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def boundary (b : Int) (i : Nat) : Int := b + i

def suffix (x : Nat → Nat) (xs : Nat → List Nat) (i : Nat) : List Bool :=
  UnaryBank.encode (x i :: xs i)

def duration (x : Nat → Nat) (xs : Nat → List Nat) (i : Nat) : Nat :=
  2 * (suffix x xs i).length + 7

def totalDuration (x : Nat → Nat) (xs : Nat → List Nat) (k : Nat) : Nat :=
  ∑ i ∈ Finset.range k, duration x xs i

theorem regular_chain (base : Nat → Int → Bool) (b : Int)
    (x : Nat → Nat) (xs : Nat → List Nat) (k : Nat)
    (hbit : ∀ i < k, base i (boundary b i) = true)
    (hlink : ∀ i < k,
      after (base i) (boundary b i + 1) (suffix x xs i) =
        prior (base (i+1)) (boundary b (i+1)) (suffix x xs (i+1))) :
    silentSegment machine
      (cfg 30 (boundary b 0) (prior (base 0) (boundary b 0) (suffix x xs 0)))
      (cfg 30 (boundary b k) (prior (base k) (boundary b k) (suffix x xs k)))
      (totalDuration x xs k) := by
  induction k with
  | zero =>
    simp [totalDuration, silentSegment, W, PASoundness.WordEventSystem.advance,
      PASoundness.WordEventSystem.wordFrom, Shared.Beeping.EventSystem.advance]
  | succ k ih =>
    have previous := ih (fun i hi => hbit i (by omega)) (fun i hi => hlink i (by omega))
    have next := regular_cycle (base k) (boundary b k) (x k) (xs k) (hbit k (by omega))
    change silentSegment machine
      (cfg 30 (boundary b k) (prior (base k) (boundary b k) (suffix x xs k)))
      (cfg 30 (boundary b k + 1) (after (base k) (boundary b k + 1) (suffix x xs k)))
      (duration x xs k) at next
    rw [hlink k (by omega)] at next
    have hb : boundary b k + 1 = boundary b (k+1) := by simp [boundary]; omega
    rw [hb] at next
    have result := segAdd machine _ _ _ (totalDuration x xs k) (duration x xs k) previous (by
      simpa [duration, suffix] using next)
    simpa [totalDuration, Finset.sum_range_succ, suffix] using result

/-- One final cycle need not leave another regular-cycle boundary: the
endpoint is the literal `after` tape, suitable also for a following cleanup. -/
theorem regular_chain_with_last (base : Nat → Int → Bool) (b : Int)
    (x : Nat → Nat) (xs : Nat → List Nat) (k : Nat)
    (hbit : ∀ i ≤ k, base i (boundary b i) = true)
    (hlink : ∀ i < k,
      after (base i) (boundary b i + 1) (suffix x xs i) =
        prior (base (i+1)) (boundary b (i+1)) (suffix x xs (i+1))) :
    silentSegment machine
      (cfg 30 (boundary b 0) (prior (base 0) (boundary b 0) (suffix x xs 0)))
      (cfg 30 (boundary b k + 1) (after (base k) (boundary b k + 1) (suffix x xs k)))
      (totalDuration x xs k + duration x xs k) := by
  have hs := regular_chain base b x xs k (fun i hi => hbit i (by omega)) hlink
  have hn := regular_cycle (base k) (boundary b k) (x k) (xs k) (hbit k (by omega))
  exact segAdd machine _ _ _ _ _ hs (by simpa [suffix, duration] using hn)

theorem totalDuration_positive (x : Nat → Nat) (xs : Nat → List Nat) (k : Nat)
    (hk : 0 < k) : 0 < totalDuration x xs k := by
  cases k with
  | zero => omega
  | succ k =>
    simp only [totalDuration, Finset.sum_range_succ]
    simp only [duration]
    omega

end Shared.Beeping.NPcoNP.NativeHalfRegularIteration
