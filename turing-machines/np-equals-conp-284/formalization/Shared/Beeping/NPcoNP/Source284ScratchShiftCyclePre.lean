import Shared.Beeping.NPcoNP.Source284ScratchShiftCycle

/-! Exact last-row configuration before a scratch shift returns. -/
set_option maxRecDepth 4096
namespace Shared.Beeping.NPcoNP.Source284ScratchShiftCyclePre

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (push flipped)
open Shared.Beeping.NPcoNP.Source284ScratchShift (written)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)

theorem return_pre (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (Source284ScratchShiftReturn.table continuation)
      ⟨2*(tail/2),payloadFold (2*certificate) (written false w),some 0⟩ (2*w.length+2) =
    ⟨2*flipped w (tail/2),2*certificate,some 6⟩ := by
  rw [Source284ScratchShiftReturn.fold_written]
  have ht : 2*w.length+2 = 1+(2*w.length+1) := by omega
  rw [ht,run_add]
  change run (Source284ScratchShiftReturn.table continuation)
    (step (Source284ScratchShiftReturn.table continuation)
      ⟨2*(tail/2),2*push (4*certificate) w,some 0⟩) _ = _
  rw [Source284ScratchShiftReturn.entry_step]
  have he : 2*(2*(tail/2)) = 4*(tail/2) := by omega
  rw [he]
  change run (Source284ScratchShiftReturn.table continuation)
    (shiftConfig 1 ⟨4*(tail/2),push (4*certificate) w,some 3⟩) _ = _
  rw [Source284ScratchShiftReturn.relocated_run]
  have hc : 2*w.length+1 = 2*w.length+1 := rfl
  rw [hc,run_add,Source284ScratchFlipReturn.reverse_pairs,Source284ScratchFlipReturn.raw_flipped]
  simp [run,step,Source284ScratchFlipReturn.table,shiftConfig,bit,Nat.testBit_zero,Nat.mul_mod] <;>
    try split_ifs
  all_goals repeat' constructor
  all_goals omega

theorem cycle_pre (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (Source284ScratchShiftCycle.table continuation)
      ⟨certificate,2*flipped w tail,some 0⟩ (4*w.length+6) =
    ⟨2*flipped w (tail/2),2*certificate,some 13⟩ := by
  have ht : 4*w.length+6 = (2*w.length+4)+(2*w.length+2) := by omega
  rw [ht,run_add]
  change run (Source284ScratchShiftPipeline.entry (Source284ScratchShiftReturn.table continuation))
    (run (Source284ScratchShiftPipeline.entry (Source284ScratchShiftReturn.table continuation)) _ _) _ = _
  rw [Source284ScratchShiftPipeline.shift_entry]
  change run (Source284ScratchShiftPipeline.entry (Source284ScratchShiftReturn.table continuation))
    (shiftConfig 1 (shiftConfig 6 ⟨2*(tail/2),payloadFold (2*certificate)
      (written false w),some 0⟩)) _ = _
  rw [Source284ScratchShiftPipeline.relocated_run,Source284ScratchShift.relocated_run,return_pre]
  rfl

end Shared.Beeping.NPcoNP.Source284ScratchShiftCyclePre
