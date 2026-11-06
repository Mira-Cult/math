import Shared.Beeping.NPcoNP.Source284ScratchCounterExtend
import Shared.Beeping.NPcoNP.Source284FlippedCounterSeed

/-! Paid initialization of the one-bit unary counter from an arbitrary high
scratch suffix, preserving the payload and the complete opposite half. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284CounterOneSeed

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)

/-- Extending a unary counter reaches and follows its supplied continuation;
the new terminator overwrites one high suffix bit. -/
theorem extend_then (continuation : Nat → Bool → Row) (w : List Bool)
    (n certificate higher fuel : Nat) :
    run (Source284ScratchCounterExtend.table continuation)
      ⟨certificate,2*flipped w (counter n higher),some 0⟩ (4*w.length+2*n+16+fuel) =
    shiftConfig 16 (run continuation
      ⟨certificate,2*flipped w (counter (n+1) (higher/2)),some 0⟩ fuel) := by
  rw [Source284ScratchScanner.run_add,Source284ScratchCounterExtend.extend_scratch]
  let c : Config := ⟨certificate,2*flipped w (counter (n+1) (higher/2)),some 0⟩
  change run (Source284ScratchCounterExtend.table continuation) (shiftConfig 16 c) fuel = _
  have he : shiftConfig 16 c = shiftConfig 4 (shiftConfig 5 (shiftConfig 1 (shiftConfig 6 c))) := by
    simp [Source284SourceRelocation.shiftConfig_add]
  rw [he,Source284ScratchCounterExtend.relocated_run,Source284CounterExtend.relocated_run,
    Source284ScratchCounterSeed.after_relocated_run,Source284ScratchFlipReturn.relocated_run]
  simp only [Source284SourceRelocation.shiftConfig_add]
  rfl

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284FlippedCounterSeed.table (Source284ScratchCounterExtend.table continuation)

def cost (width : Nat) : Nat := (4*width+14)+(4*width+16)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (32+states) (table continuation) := by
  have he := Source284ScratchCounterExtend.closed states continuation hn hv
  have hs := Source284FlippedCounterSeed.closed (16+states)
    (Source284ScratchCounterExtend.table continuation) (by omega) he
  have hid : 16+(16+states)=32+states := by omega
  rw [hid] at hs
  exact hs

/-- Two paid finite passes seed and extend the counter to one. The two
overwritten high suffix bits are accounted for by the two divisions. -/
theorem seed_then (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate higher fuel : Nat) :
    run (table continuation) ⟨certificate,2*flipped w higher,some 0⟩ (cost w.length+fuel) =
    shiftConfig 32 (run continuation
      ⟨certificate,2*flipped w (counter 1 ((higher/2)/2)),some 0⟩ fuel) := by
  have ht : cost w.length+fuel = (4*w.length+14)+((4*w.length+16)+fuel) := by simp [cost]; omega
  rw [ht]
  unfold table
  rw [Source284FlippedCounterSeed.seed_then,extend_then,Source284SourceRelocation.shiftConfig_add]

end Shared.Beeping.NPcoNP.Source284CounterOneSeed
