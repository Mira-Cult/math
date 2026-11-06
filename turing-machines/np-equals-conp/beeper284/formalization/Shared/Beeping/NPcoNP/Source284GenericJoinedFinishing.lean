import Shared.Beeping.NPcoNP.Source284FramedJoin
import Shared.Beeping.NPcoNP.Source284InputRunwayClear

/-! The paid joined-frame finishing path with arbitrary retained tails. This
removes the previous dependence on one quadratic-loader tail formula. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284GenericJoinedFinishing

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284FramedJoin.finishing (Source284InputRunwayClear.table continuation)

def cost (input witness : List Bool) := Source284FramedJoin.finishingCost input witness+6

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (247+states) (table continuation) := by
  have hc := Source284InputRunwayClear.closed states continuation hn hv
  have hf := Source284FramedJoin.finishing_closed (6+states)
    (Source284InputRunwayClear.table continuation) (by omega) hc
  simpa [table,show 241+(6+states)=247+states by omega] using hf

/-- For any retained input and witness tails, the real finite table reaches
the joined bit stream and preserves those tails at the declared positions. -/
theorem finish_then (states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (inputTail witnessTail fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    run (table continuation)
      ⟨2*flipped (input++[false]) inputTail,2*flipped witness witnessTail,some 0⟩
      (cost input witness+fuel) =
    shiftConfig 247 (run continuation
      ⟨8*inputTail,stack (Source284JoinedFrames.joinedBits input witness) (witnessTail/2),some 0⟩ fuel) := by
  have hc := Source284InputRunwayClear.closed states continuation hn hv
  have ht : cost input witness+fuel = (4*witness.length+7)+((6*witness.length+11)+
      (Source284JoinedTripleAdapter.cost input+((2*input.length+10)+(6+fuel)))) := by
    simp [cost,Source284FramedJoin.finishingCost]; omega
  rw [ht]
  unfold table Source284FramedJoin.finishing
  rw [Source284ShiftContinue.cycle_then,Source284WitnessReframe.normalize_then]
  have he : 2*(2*(2*flipped (input++[false]) inputTail)) =
      8*flipped (input++[false]) inputTail := by omega
  rw [he]
  change shiftConfig 14 (shiftConfig 68 (run
    (Source284JoinedTripleAdapter.table (Source284TripleFrameJoin.table
      (Source284InputRunwayClear.table continuation)))
    ⟨8*flipped (input++[false]) inputTail,
      encodeFrame witness (2*(witnessTail/2)+1),some 0⟩ _)) = _
  rw [Source284JoinedTripleAdapter.reframe_then (20+(6+states))
    (Source284TripleFrameJoin.table (Source284InputRunwayClear.table continuation))
    input inputTail (encodeFrame witness (2*(witnessTail/2)+1)) ((2*input.length+10)+(6+fuel))
    (by omega) (Source284TripleFrameJoin.closed (6+states) (Source284InputRunwayClear.table continuation)
      (by omega) hc),Source284TripleFrameJoin.join_then,Source284InputRunwayClear.clear_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]

end Shared.Beeping.NPcoNP.Source284GenericJoinedFinishing
