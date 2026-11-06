import Shared.Beeping.NPcoNP.Source284ScratchShiftReturn

/-! A finite shift-and-return cycle, plus a structurally generated finite
sequence of any fixed number of cycles. The number of cycles is compiled into
the table, not read dynamically from the input. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchShiftCycle

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchShiftPipeline.entry (Source284ScratchShiftReturn.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (14+states) (table continuation) := by
  have hr := Source284ScratchShiftReturn.closed states continuation hn hv
  have he := Source284ScratchShiftPipeline.entry_closed (7+states)
    (Source284ScratchShiftReturn.table continuation) (by omega) hr
  have h : 7+(7+states) = 14+states := by omega
  rw [h] at he
  exact he

theorem shift_nested (c : Config) :
    shiftConfig 1 (shiftConfig 6 (shiftConfig 1 (shiftConfig 6 c))) = shiftConfig 14 c := by
  cases c with
  | mk left right state => cases state <;> simp [shiftConfig] <;> omega

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 14 c) clock = shiftConfig 14 (run continuation c clock) := by
  rw [← shift_nested c]
  change run (Source284ScratchShiftPipeline.entry (Source284ScratchShiftReturn.table continuation)) _ _ = _
  rw [Source284ScratchShiftPipeline.relocated_run,Source284ScratchShift.relocated_run,
    Source284ScratchShiftReturn.relocated_run,Source284ScratchFlipReturn.relocated_run,shift_nested]

/-- One cycle shifts the stream and physically returns to its boundary,
preserving the certificate and leaving one additional zero before it. -/
theorem cycle_frame (continuation : Nat → Bool → Row) (w : List Bool) (certificate tail : Nat) :
    run (table continuation) ⟨certificate,2*flipped w tail,some 0⟩ (4*w.length+7) =
      ⟨2*certificate,2*flipped w (tail/2),some 14⟩ := by
  have ht : 4*w.length+7 = (2*w.length+4)+(2*w.length+3) := by omega
  rw [ht,Source284PayloadPop.run_add]
  change run (Source284ScratchShiftPipeline.entry (Source284ScratchShiftReturn.table continuation))
    (run (Source284ScratchShiftPipeline.entry (Source284ScratchShiftReturn.table continuation)) _ _) _ = _
  rw [Source284ScratchShiftPipeline.shift_entry]
  change run (Source284ScratchShiftPipeline.entry (Source284ScratchShiftReturn.table continuation))
    (shiftConfig 1 (shiftConfig 6 ⟨2*(tail/2),Source284Parser.payloadFold (2*certificate)
      (Source284ScratchShift.written false w),some 0⟩)) _ = _
  rw [Source284ScratchShiftPipeline.relocated_run,Source284ScratchShift.relocated_run,
    Source284ScratchShiftReturn.return_frame]
  rfl

/-- The caller chooses `count` at table-construction time. This is an
explicit finite code generator, not an input-dependent runtime loop. -/
def repeatTable : Nat → (Nat → Bool → Row) → (Nat → Bool → Row)
  | 0, continuation => continuation
  | count+1, continuation => table (repeatTable count continuation)

theorem repeat_closed (count states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (14*count+states) (repeatTable count continuation) := by
  induction count with
  | zero => simpa [repeatTable] using hv
  | succ count ih =>
    have h := closed (14*count+states) (repeatTable count continuation) (by omega) ih
    have he : 14+(14*count+states) = 14*(count+1)+states := by omega
    rw [he] at h
    exact h

/-- Repeating a finite number of compiled cycles loses exactly one ignored
high-suffix bit per cycle and moves the certificate boundary by that many
zero cells. The source clock and state count both include every copy. -/
theorem repeat_run (count : Nat) (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (repeatTable count continuation) ⟨certificate,2*flipped w tail,some 0⟩
      (count*(4*w.length+7)) =
      ⟨2^count*certificate,2*flipped w (tail/2^count),some (14*count)⟩ := by
  induction count generalizing certificate tail with
  | zero => simp [repeatTable,run]
  | succ count ih =>
    have ht : (count+1)*(4*w.length+7) = (4*w.length+7)+count*(4*w.length+7) := by ring
    rw [ht]
    change run (table (repeatTable count continuation)) _ _ = _
    rw [Source284PayloadPop.run_add,cycle_frame]
    change run (table (repeatTable count continuation))
      (shiftConfig 14 ⟨2*certificate,2*flipped w (tail/2),some 0⟩) _ = _
    rw [relocated_run,ih]
    have hm : 2^count*(2*certificate) = 2^(count+1)*certificate := by
      rw [pow_succ]
      ring
    have hd : (tail/2)/2^count = tail/2^(count+1) := by
      rw [Nat.div_div_eq_div_mul,pow_succ]
      congr 1
      ring
    have hs : 14+14*count = 14*(count+1) := by omega
    simp only [shiftConfig,Option.map_some,hm,hd,hs]

end Shared.Beeping.NPcoNP.Source284ScratchShiftCycle
