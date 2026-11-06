import Shared.Beeping.NPcoNP.Source284LengthGrowRound
import Shared.Beeping.NPcoNP.Source284ScratchShiftCyclePre

/-! The growth path's final turn, exposed for a progress-sensitive loop. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284LengthGrowPre

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284LengthGrowRound

def preTime (tokens xs rest : List Bool) : Nat :=
  ((4*tokens.length+6)+(4*(xs.length+rest.length)+12)) +
    ((4*((xs++rest)++[false]).length+7)+(4*((xs++rest)++[false]).length+6))

theorem grow_pre (tokens xs rest : List Bool) (certificate tail : Nat) :
    run grow ⟨pairTape tokens certificate,2*zeros xs (flipped (rest++[false]) tail),some 0⟩
      (preTime tokens xs rest) =
    ⟨2*flipped ((xs++rest)++[false]) (tail/4),
      4*pairTape (List.replicate tokens.length false) certificate,some 45⟩ := by
  unfold preTime grow
  rw [run_add,Source284MatchReset.reset]
  change run (Source284MatchReset.table (Source284ScratchShiftCycle.repeatTable 2 sink))
    (shiftConfig 7 (shiftConfig 5 (shiftConfig 6
      ⟨pairTape (List.replicate tokens.length false) certificate,
        2*flipped ((xs++rest)++[false]) tail,some 0⟩))) _ = _
  unfold Source284MatchReset.table
  rw [Source284UnaryClear.relocated_run,Source284PayloadReset.relocated_run,
    Source284ScratchFlipReturn.relocated_run]
  change shiftConfig 7 (shiftConfig 5 (shiftConfig 6
    (run (Source284ScratchShiftCycle.table (Source284ScratchShiftCycle.table sink)) _ _))) = _
  rw [run_add,Source284ScratchShiftCycle.cycle_frame]
  change shiftConfig 7 (shiftConfig 5 (shiftConfig 6
    (run (Source284ScratchShiftCycle.table (Source284ScratchShiftCycle.table sink))
      (shiftConfig 14 ⟨2*pairTape (List.replicate tokens.length false) certificate,
        2*flipped ((xs++rest)++[false]) (tail/2),some 0⟩) _))) = _
  rw [Source284ScratchShiftCycle.relocated_run,Source284ScratchShiftCyclePre.cycle_pre]
  have hd : (tail/2)/2 = tail/4 := by omega
  simp [shiftConfig,hd]
  ring

def roundPreTime (xs rest : List Bool) (b : Bool) : Nat :=
  compareTime xs.length + (2+preTime (List.replicate xs.length true) (xs++[b]) rest)

theorem grow_round_pre (xs rest : List Bool) (b : Bool) (certificate tail : Nat) :
    run table ⟨pairTape (List.replicate xs.length false) certificate,
      2*flipped ((xs++b::rest)++[false]) tail,some 0⟩ (roundPreTime xs rest b) =
    ⟨2*flipped ((xs++b::rest)++[false]) (tail/4),
      pairTape (List.replicate (xs.length+1) false) certificate,some 98⟩ := by
  unfold roundPreTime compareTime table
  rw [run_add,Source284MatchLoopComplete.more_payload]
  change run (Source284MatchLoop.table dispatch)
    (shiftConfig 48 ⟨pairTape (List.replicate xs.length true) certificate,
      2*zeros (xs++[b]) (flipped (rest++[false]) tail),some 1⟩) _ = _
  rw [Source284MatchLoop.relocated_run,run_add,enter 1 _ _ (Or.inl rfl)]
  change shiftConfig 48 (run dispatch
    (shiftConfig 5 ⟨pairTape (List.replicate xs.length true) certificate,
      2*zeros (xs++[b]) (flipped (rest++[false]) tail),some 0⟩) _) = _
  have hv : Valid 47 ⟨pairTape (List.replicate xs.length true) certificate,
      2*zeros (xs++[b]) (flipped (rest++[false]) tail),some 0⟩ := by
    intro q hq; simp at hq; omega
  rw [grow_run _ hv,grow_pre]
  simp only [List.length_replicate]
  rw [token_prepend]
  simp [shiftConfig,List.append_assoc]

theorem preTime_succ (xs rest : List Bool) (b : Bool) :
    roundPreTime xs rest b + 1 = growTime xs rest b := by
  unfold roundPreTime preTime growTime
  simp only [List.length_replicate]
  omega

end Shared.Beeping.NPcoNP.Source284LengthGrowPre
