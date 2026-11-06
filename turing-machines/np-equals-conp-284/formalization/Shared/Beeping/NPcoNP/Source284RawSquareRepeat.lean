import Shared.Beeping.NPcoNP.Source284SquareRepeatCost
import Shared.Beeping.NPcoNP.Source284DoubleLengthTokens

/-! Raw-input initialization followed by a fixed number of square-growth
passes. The pass count is part of the finite table, not a runtime oracle. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284RawSquareRepeat

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284SquareRepeat (repeatTable repeatCost)

def setup (k : Nat) (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284FlippedCounterSeed.table (repeatTable k continuation)

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284DoubleLengthTokens.description (16+(110*k+states)) (setup k continuation)

def totalCost (k : Nat) (w : List Bool) : Nat :=
  Source284DoubleLengthTokens.totalCost w + (4*(w++[false]).length+14) +
    repeatCost k w.length 0 (w++[false]).length

theorem setup_closed (k states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (16+(110*k+states)) (setup k continuation) := by
  have hr := Source284SquareRepeat.repeat_closed k states continuation hn hv
  exact Source284FlippedCounterSeed.closed (110*k+states) (repeatTable k continuation) (by omega) hr

/-- A fixed source table produces `k*n^2` counter marks from every raw frame,
then executes its continuation. -/
theorem source_then (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) (totalCost k w+fuel) =
    toSource (shiftConfig (465+110*k) (run continuation
      ⟨pairTape (List.replicate w.length false) (pairTape (List.replicate w.length false) certificate),
        2*flipped (w++[false]) (counter (k*(w.length*w.length))
          (halves (k*(w.length*w.length)) (Source284DoubleLengthTokens.retained w.length suffix/2))),some 0⟩ fuel)) := by
  have hp := Source284DoubleLengthTokens.source_then (16+(110*k+states)) (setup k continuation) w certificate suffix
    ((4*(w++[false]).length+14)+(repeatCost k w.length 0 (w++[false]).length+fuel))
    (by omega) (setup_closed k states continuation hn hv)
  have ht : totalCost k w+fuel = Source284DoubleLengthTokens.totalCost w +
      ((4*(w++[false]).length+14)+(repeatCost k w.length 0 (w++[false]).length+fuel)) := by
    simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284DoubleLengthTokens.description (16+(110*k+states)) (setup k continuation))
    (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) _ = _
  rw [hp]
  unfold setup
  rw [Source284FlippedCounterSeed.seed_then,Source284SquareRepeat.repeat_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  simp

/-- The pass portion has a concrete polynomial upper bound for every fixed k. -/
theorem passCost_le (k : Nat) (w : List Bool) :
    repeatCost k w.length 0 (w++[false]).length ≤
      k*(w.length^4+2*w.length^3+4*w.length^2*(w.length+1)+35*w.length^2+44*w.length+26)+
        w.length^4*k*k := by
  simpa using Source284SquareRepeatCost.repeatCost_le k w.length (w.length+1)

end Shared.Beeping.NPcoNP.Source284RawSquareRepeat
