import Shared.Beeping.NPcoNP.Source284CleanWorkspace

/-! A fixed number of finite workspace passes. The count is compiled into the
table; it is not an input-dependent runtime loop. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284RepeatWorkspace

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284LengthGrowLoop (totalTime quarters)
open Shared.Beeping.NPcoNP.Source284LengthGrowSource (setupCost)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)

def round (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284LengthGrowRawContinue.setup (Source284CleanWorkspace.table continuation)

theorem round_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (226+states) (round continuation) := by
  have hc := Source284CleanWorkspace.closed states continuation hn hv
  have hs := Source284LengthGrowRawContinue.setup_closed (79+states)
    (Source284CleanWorkspace.table continuation) (by omega) hc
  have he : 147+(79+states) = 226+states := by omega
  rw [he] at hs
  exact hs

def roundCost (w : List Bool) : Nat :=
  setupCost w + (totalTime [] w + Source284CleanWorkspace.workCost w.length (w++[false]).length)

def nextTail (n tail : Nat) : Nat := halves n (quarters n ((tail/2)/2)/2)

/-- One pass reconstructs the token tape from the input, consumes and erases
it, and leaves `3*(n+1)` zero cells directly in front of the certificate. -/
theorem round_then (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail fuel : Nat) :
    run (round continuation) ⟨certificate,2*flipped (w++[false]) tail,some 0⟩ (roundCost w+fuel) =
    shiftConfig 226 (run continuation
      ⟨2^(3*(w.length+1))*certificate,2*flipped (w++[false]) (nextTail w.length tail),some 0⟩ fuel) := by
  have ht : roundCost w+fuel = setupCost w +
      (totalTime [] w + (Source284CleanWorkspace.workCost w.length (w++[false]).length+fuel)) := by
    simp [roundCost]; omega
  rw [ht]
  unfold round
  rw [Source284LengthGrowRawContinue.setup_then,Source284CleanWorkspace.workspace_then,
    Source284SourceRelocation.shiftConfig_add]
  rfl

theorem roundCost_formula (w : List Bool) :
    3*roundCost w = 4*w.length*w.length*w.length+111*w.length*w.length+404*w.length+309 := by
  have h := Source284LengthGrowTime.zero_formula w
  rw [roundCost]
  simp only [setupCost,List.length_append,List.length_singleton,Source284CleanWorkspace.workCost_formula]
  nlinarith

/-- The repetition count is part of the finite program description. -/
def repeatTable : Nat → (Nat → Bool → Row) → (Nat → Bool → Row)
  | 0, continuation => continuation
  | k+1, continuation => round (repeatTable k continuation)

theorem repeat_closed (k states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (226*k+states) (repeatTable k continuation) := by
  induction k with
  | zero => simpa [repeatTable] using hv
  | succ k ih =>
    have h := round_closed (226*k+states) (repeatTable k continuation) (by omega) ih
    have he : 226+(226*k+states) = 226*(k+1)+states := by omega
    rw [he] at h
    exact h

def iterateTail : Nat → Nat → Nat → Nat
  | 0, _, tail => tail
  | k+1, n, tail => iterateTail k n (nextTail n tail)

theorem repeat_then (k : Nat) (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail fuel : Nat) :
    run (repeatTable k continuation) ⟨certificate,2*flipped (w++[false]) tail,some 0⟩
      (k*roundCost w+fuel) =
    shiftConfig (226*k) (run continuation
      ⟨2^(k*(3*(w.length+1)))*certificate,
        2*flipped (w++[false]) (iterateTail k w.length tail),some 0⟩ fuel) := by
  induction k generalizing certificate tail with
  | zero => simp [repeatTable,iterateTail,shiftConfig]
  | succ k ih =>
    have ht : (k+1)*roundCost w+fuel = roundCost w+(k*roundCost w+fuel) := by ring
    rw [ht]
    change run (round (repeatTable k continuation)) _ _ = _
    rw [round_then,ih,Source284SourceRelocation.shiftConfig_add]
    have hs : 226+226*k = 226*(k+1) := by omega
    have hp : 2^(k*(3*(w.length+1)))*(2^(3*(w.length+1))*certificate) =
        2^((k+1)*(3*(w.length+1)))*certificate := by
      rw [← Nat.mul_assoc,← pow_add]
      congr 2 <;> ring
    simp only [hs,hp,iterateTail]

end Shared.Beeping.NPcoNP.Source284RepeatWorkspace
