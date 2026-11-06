import Shared.Beeping.NPcoNP.Source284OneRetry
import Shared.Beeping.NPcoNP.Source284ScratchShiftLoop

/-! The exact penultimate configurations of the retry operation. These make
it possible to redirect only its final transition back to the comparator. -/
set_option maxRecDepth 2048
namespace Shared.Beeping.NPcoNP.Source284RetryGrowPre

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)
open Shared.Beeping.NPcoNP.Source284ScratchShift (written)

/-- The general shift-cycle table, one step before the restored boundary. -/
theorem shift_pre (continuation : Nat → Bool → Row) (w : List Bool) (certificate tail : Nat) :
    run (Source284ScratchShiftCycle.table continuation)
      ⟨certificate,2*flipped w tail,some 0⟩ (4*w.length+6) =
      ⟨2*flipped w (tail/2),2*certificate,some 13⟩ := by
  have ht : 4*w.length+6 = (2*w.length+4)+(2*w.length+2) := by omega
  rw [ht,run_add]
  change run (Source284ScratchShiftPipeline.entry (Source284ScratchShiftReturn.table continuation))
    (run (Source284ScratchShiftPipeline.entry (Source284ScratchShiftReturn.table continuation)) _ _) _ = _
  rw [Source284ScratchShiftPipeline.shift_entry]
  change run (Source284ScratchShiftPipeline.entry (Source284ScratchShiftReturn.table continuation))
    (shiftConfig 1 (shiftConfig 6 ⟨2*(tail/2),payloadFold (2*certificate) (written false w),some 0⟩)) _ = _
  rw [Source284ScratchShiftPipeline.relocated_run,Source284ScratchShift.relocated_run,
    Source284ScratchShiftLoop.return_pre]
  rfl

/-- After the reset and the first shift, the second shift reaches its final
turn with the new unary pair already present. -/
theorem grow_pre (continuation : Nat → Bool → Row) (tokens xs rest : List Bool)
    (certificate tail : Nat) :
    run (Source284MatchGrow.table continuation)
      ⟨pairTape tokens certificate,2*zeros xs (flipped (rest++[false]) tail),some 0⟩
      (4*tokens.length+12*(xs.length+rest.length)+39) =
    ⟨2*flipped ((xs++rest)++[false]) (tail/4),
      pairTape (List.replicate (tokens.length+1) false) certificate,some 45⟩ := by
  let w := (xs++rest)++[false]
  let left := pairTape (List.replicate tokens.length false) certificate
  have hw : w.length = xs.length+rest.length+1 := by simp [w]; omega
  have ht : 4*tokens.length+12*(xs.length+rest.length)+39 =
      ((4*tokens.length+6)+(4*(xs.length+rest.length)+12))+
        ((4*w.length+7)+(4*w.length+6)) := by rw [hw]; ring
  rw [ht,run_add]
  change run (Source284MatchReset.table (Source284ScratchShiftCycle.repeatTable 2 continuation))
    (run (Source284MatchReset.table (Source284ScratchShiftCycle.repeatTable 2 continuation)) _ _) _ = _
  rw [Source284MatchReset.reset]
  change run (Source284UnaryClear.table (Source284PayloadReset.table
      (Source284ScratchShiftCycle.table (Source284ScratchShiftCycle.table continuation))))
    (shiftConfig 7 (shiftConfig 5 (shiftConfig 6 ⟨left,2*flipped w tail,some 0⟩))) _ = _
  rw [Source284UnaryClear.relocated_run,Source284PayloadReset.relocated_run,
    Source284ScratchFlipReturn.relocated_run,run_add,Source284ScratchShiftCycle.cycle_frame]
  change shiftConfig 7 (shiftConfig 5 (shiftConfig 6
    (run (Source284ScratchShiftCycle.table (Source284ScratchShiftCycle.table continuation))
      (shiftConfig 14 ⟨2*left,2*flipped w (tail/2),some 0⟩) _))) = _
  rw [Source284ScratchShiftCycle.relocated_run,shift_pre]
  have hs : (tail/2)/2 = tail/4 := by rw [Nat.div_div_eq_div_mul]
  have hl : 2*(2*left) = pairTape (List.replicate (tokens.length+1) false) certificate := by
    calc
      2*(2*left) = 2^2*left := by ring
      _ = _ := Source284MatchGrow.add_zero_pair tokens.length certificate
  simp [shiftConfig,hs,hl,w,List.append_assoc]

/-- One retry reaches state 96 one step before restarting, with all data
already restored and the token count incremented. -/
theorem retry_pre (continuation : Nat → Bool → Row) (w rest : List Bool) (b : Bool)
    (certificate tail : Nat) :
    run (Source284OneRetry.table continuation)
      ⟨pairTape (List.replicate w.length false) certificate,
        2*flipped ((w++b::rest)++[false]) tail,some 0⟩
      ((4*w.length*w.length+20*w.length+16)+(4*w.length+12*(w++b::rest).length+39)) =
    ⟨2*flipped ((w++b::rest)++[false]) (tail/4),
      pairTape (List.replicate (w.length+1) false) certificate,some 96⟩ := by
  have hlen : (w++b::rest).length = (w++[b]).length+rest.length := by simp; omega
  rw [hlen,run_add]
  change run (Source284MatchLoop.table (Source284RetryDispatch.table continuation))
    (run (Source284MatchLoop.table (Source284RetryDispatch.table continuation)) _ _) _ = _
  rw [Source284MatchLoopComplete.more_payload]
  change run (Source284MatchLoop.table (Source284RetryDispatch.table continuation))
    (shiftConfig 48 ⟨pairTape (List.replicate w.length true) certificate,
      2*zeros (w++[b]) (flipped (rest++[false]) tail),some 1⟩) _ = _
  rw [Source284MatchLoop.relocated_run]
  have hp : 0 < 4*w.length+12*((w++[b]).length+rest.length)+39 := by omega
  rw [Source284RetryDispatch.run_retry _ _ _ _ hp]
  have h := grow_pre continuation (List.replicate w.length true) (w++[b]) rest certificate tail
  simp only [List.length_replicate] at h
  rw [h]
  simp [shiftConfig,List.append_assoc]

end Shared.Beeping.NPcoNP.Source284RetryGrowPre
