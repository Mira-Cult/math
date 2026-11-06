import Shared.Beeping.NPcoNP.Source284RawSquareRepeat

/-! A fixed number of square-growth passes supplies a fixed quadratic
coefficient on the certificate side. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284RawScaledQuadratic

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284RawSquareRepeat.description k (21+states) (Source284CountedShift.table continuation)

def totalCost (k : Nat) (w : List Bool) : Nat :=
  Source284RawSquareRepeat.totalCost k w+(k*(w.length*w.length)+1)*(4*(w++[false]).length+7)

def retained (k n suffix : Nat) : Nat :=
  halves (k*(n*n)) (Source284DoubleLengthTokens.retained n suffix/2)

/-- For each compile-time coefficient k, a fixed encoded source table
creates `k*n^2+1` contiguous zero cells before its continuation. -/
theorem source_then (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) (totalCost k w+fuel) =
    toSource (shiftConfig (486+110*k) (run continuation
      ⟨2^(k*(w.length*w.length)+1)*
          pairTape (List.replicate w.length false) (pairTape (List.replicate w.length false) certificate),
        2*flipped (w++[false]) (retained k w.length suffix),some 0⟩ fuel)) := by
  have hc := Source284CountedShift.closed states continuation hn hv
  have hp := Source284RawSquareRepeat.source_then k (21+states) (Source284CountedShift.table continuation)
    w certificate suffix ((k*(w.length*w.length)+1)*(4*(w++[false]).length+7)+fuel) (by omega) hc
  have ht : totalCost k w+fuel = Source284RawSquareRepeat.totalCost k w+
      ((k*(w.length*w.length)+1)*(4*(w++[false]).length+7)+fuel) := by simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284RawSquareRepeat.description k (21+states) (Source284CountedShift.table continuation))
    (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) _ = _
  rw [hp,Source284CountedShift.countdown_after]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have he : 465+110*k+14+1+6 = 486+110*k := by omega
  rw [he]
  rfl

end Shared.Beeping.NPcoNP.Source284RawScaledQuadratic
