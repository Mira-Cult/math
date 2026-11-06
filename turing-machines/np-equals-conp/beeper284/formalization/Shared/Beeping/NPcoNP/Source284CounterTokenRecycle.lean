import Shared.Beeping.NPcoNP.Source284PreparedPowerRunway
import Shared.Beeping.NPcoNP.Source284ScratchSentinel

/-! A paid finite source-table adapter converts an odd-length unary counter
into a reusable paired-zero token block, preserving the old tape behind it.
The input counter and all protected data are explicit preconditions. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284CounterTokenRecycle

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchSentinel.special (Source284CountedShift.table continuation)

def cost (n width : Nat) : Nat := (2*n+2)*(4*width+7)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (35+states) (table continuation) := by
  have hc := Source284CountedShift.closed states continuation hn hv
  have hs := Source284ScratchSentinel.closed (21+states) (Source284CountedShift.table continuation)
    (by omega) hc
  have he : 14+(21+states)=35+states := by omega
  rw [he] at hs
  exact hs

theorem paired_value (n tail : Nat) :
    2^(2*n+1)*(2*tail+1) = pairTape (List.replicate n false) tail := by
  rw [Source284UnaryPairScanner.zero_pairTape,Source284ScratchSentinel.unaryPairs_stack,pow_succ]
  ring

/-- The actual table adds a marker, consumes exactly `2*n+1` unary one
bits and the terminating zero, and installs `n` paired-zero tokens. -/
theorem recycle_then (n : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (tail higher fuel : Nat) :
    run (table continuation) ⟨tail,2*flipped w (counter (2*n+1) higher),some 0⟩
      (cost n w.length+fuel) =
    shiftConfig 35 (run continuation
      ⟨pairTape (List.replicate n false) tail,2*flipped w higher,some 0⟩ fuel) := by
  have ht : cost n w.length+fuel = (4*w.length+7)+
      ((2*n+1)*(4*w.length+7)+fuel) := by simp [cost]; ring
  rw [ht,Source284ScratchScanner.run_add]
  change run (Source284ScratchSentinel.special (Source284CountedShift.table continuation))
    (run (Source284ScratchSentinel.special (Source284CountedShift.table continuation)) _ _) _ = _
  rw [Source284ScratchSentinel.special_frame]
  have hc : counter (2*n+1) higher/2 = counter (2*n) higher := by
    change (2*counter (2*n) higher+1)/2 = _
    omega
  rw [hc]
  change run (Source284ScratchSentinel.special (Source284CountedShift.table continuation))
    (shiftConfig 14 ⟨2*tail+1,2*flipped w (counter (2*n) higher),some 0⟩) _ = _
  rw [Source284ScratchSentinel.continuation_run,Source284CountedShift.countdown_after,
    paired_value]
  simp only [Source284SourceRelocation.shiftConfig_add]

end Shared.Beeping.NPcoNP.Source284CounterTokenRecycle
