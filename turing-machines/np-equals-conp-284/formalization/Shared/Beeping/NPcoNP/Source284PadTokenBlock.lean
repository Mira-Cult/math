import Shared.Beeping.NPcoNP.Source284ScratchUnaryRunway
import Shared.Beeping.NPcoNP.Source284UnaryPairScanner
import Shared.Beeping.NPcoNP.Source284SourceRelocation

/-! Four paid scratch shifts add two zero-pair tokens to a prepared unary
block. The arbitrary higher scratch suffix is tracked exactly. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284PadTokenBlock

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

theorem repeat_continuation (count : Nat) (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (Source284ScratchShiftCycle.repeatTable count continuation) (shiftConfig (14*count) c) fuel =
      shiftConfig (14*count) (run continuation c fuel) := by
  induction count with
  | zero => simp [Source284ScratchShiftCycle.repeatTable,shiftConfig]
  | succ count ih =>
    change run (Source284ScratchShiftCycle.table (Source284ScratchShiftCycle.repeatTable count continuation))
      (shiftConfig (14*(count+1)) c) fuel = _
    have he : shiftConfig (14*(count+1)) c = shiftConfig 14 (shiftConfig (14*count) c) := by
      rw [Source284SourceRelocation.shiftConfig_add]
      have hn : 14*(count+1)=14+14*count := by omega
      rw [hn]
    rw [he,Source284ScratchShiftCycle.relocated_run,ih,Source284SourceRelocation.shiftConfig_add]
    have hn : 14+14*count=14*(count+1) := by omega
    rw [hn]

theorem pairTape_add_two (n certificate : Nat) :
    2^4*pairTape (List.replicate n false) certificate = pairTape (List.replicate (n+2) false) certificate := by
  rw [Source284UnaryPairScanner.zero_pairTape,Source284UnaryPairScanner.zero_pairTape,
    Source284ScratchSentinel.unaryPairs_stack,Source284ScratchSentinel.unaryPairs_stack]
  have he : 2*(n+2)=2*n+4 := by omega
  rw [he,pow_add]
  ring

/-- The table writes four zero cells, advances the scratch boundary four
times, and then follows its supplied continuation. -/
theorem pad_then (continuation : Nat → Bool → Row) (n : Nat) (w : List Bool)
    (certificate higher fuel : Nat) :
    run (Source284ScratchShiftCycle.repeatTable 4 continuation)
      ⟨pairTape (List.replicate n false) certificate,2*flipped w higher,some 0⟩
      (4*(4*w.length+7)+fuel) =
    shiftConfig 56 (run continuation
      ⟨pairTape (List.replicate (n+2) false) certificate,2*flipped w (higher/2^4),some 0⟩ fuel) := by
  rw [Source284ScratchScanner.run_add,Source284ScratchShiftCycle.repeat_run,pairTape_add_two]
  change run (Source284ScratchShiftCycle.repeatTable 4 continuation)
    (shiftConfig (14*4) ⟨pairTape (List.replicate (n+2) false) certificate,
      2*flipped w (higher/2^4),some 0⟩) fuel = _
  rw [repeat_continuation]

end Shared.Beeping.NPcoNP.Source284PadTokenBlock
