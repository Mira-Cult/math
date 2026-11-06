import Shared.Beeping.NPcoNP.Source284LengthGrowRound
import Shared.Beeping.NPcoNP.Source284ScratchCounterExtend

/-! The equality path's exact last turn, before its reference sink. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284LengthEqualPre

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add push_append)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (push flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284LengthGrowRound

theorem payload_reset_pre (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (Source284PayloadReset.table continuation)
      ⟨certificate,2*zeros w (flipped [false] tail),some 0⟩ (4*w.length+11) =
    ⟨2*flipped (w++[false]) tail,certificate,some 10⟩ := by
  have ht : 4*w.length+11 = 1+(2*w.length+(2+(2+(2*(w++[false]).length+4)))) := by simp; omega
  rw [ht,run_add]
  change run (Source284PayloadReset.table continuation)
    (step (Source284PayloadReset.table continuation)
      ⟨certificate,2*zeros w (flipped [false] tail),some 0⟩) _ = _
  rw [Source284PayloadReset.startup,run_add,Source284PayloadReset.zero_prefix]
  change run (Source284PayloadReset.table continuation)
    ⟨push (2*certificate) w,bit false+2+4*flipped [] tail,some 1⟩ _ = _
  rw [run_add,Source284PayloadReset.first_one]
  have hp : 4*push (2*certificate) w+2*bit false+1 = push (2*certificate) (w++[false]) := by
    rw [Source284ScratchFlipReturn.push_snoc]
  rw [hp]
  change run (Source284PayloadReset.table continuation) ⟨push (2*certificate) (w++[false]),4*tail,some 3⟩ _ = _
  rw [run_add,Source284PayloadReset.turn,Source284PayloadReset.relocated_run,
    Source284ScratchCounterExtend.return_pre]
  rfl

theorem equal_pre (w : List Bool) (certificate tail : Nat) :
    run equal ⟨pairTape (List.replicate w.length true) certificate,
      2*zeros w (flipped [false] tail),some 0⟩ ((4*w.length+6)+(4*w.length+11)) =
    ⟨2*flipped (w++[false]) tail,pairTape (List.replicate w.length false) certificate,some 17⟩ := by
  unfold equal Source284MatchReset.table
  rw [run_add]
  have hc := Source284UnaryClear.clear (Source284PayloadReset.table sink)
    (List.replicate w.length true) certificate (zeros w (flipped [false] tail))
  simp only [List.length_replicate] at hc
  rw [hc]
  change run (Source284UnaryClear.table (Source284PayloadReset.table sink))
    (shiftConfig 7 ⟨pairTape (List.replicate w.length false) certificate,
      2*zeros w (flipped [false] tail),some 0⟩) _ = _
  rw [Source284UnaryClear.relocated_run,payload_reset_pre]
  simp [shiftConfig]

def equalPreTime (n : Nat) : Nat := compareTime n+(2+((4*n+6)+(4*n+11)))

theorem equal_round_pre (w : List Bool) (certificate tail : Nat) :
    run table ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) tail,some 0⟩ (equalPreTime w.length) =
    ⟨2*flipped (w++[false]) tail,pairTape (List.replicate w.length false) certificate,some 117⟩ := by
  unfold equalPreTime compareTime table
  rw [run_add,Source284MatchLoopComplete.equal_length]
  change run (Source284MatchLoop.table dispatch)
    (shiftConfig 48 ⟨pairTape (List.replicate w.length true) certificate,
      2*zeros w (flipped [false] tail),some 2⟩) _ = _
  rw [Source284MatchLoop.relocated_run,run_add,enter 2 _ _ (Or.inr rfl)]
  change shiftConfig 48 (run dispatch
    (shiftConfig 52 ⟨pairTape (List.replicate w.length true) certificate,
      2*zeros w (flipped [false] tail),some 0⟩) _) = _
  rw [equal_run,equal_pre]
  rfl

theorem equalPreTime_succ (n : Nat) : equalPreTime n+1 = equalTime n := by
  unfold equalPreTime equalTime
  omega

end Shared.Beeping.NPcoNP.Source284LengthEqualPre
