import Shared.Beeping.NPcoNP.Source284ScratchShiftPipeline

/-! A finite source-table return after the scratch shifter. It reuses the
self-delimiting reverse scanner, restores the complete certificate, and
leaves one additional zero cell on the certificate side of the head. This
is an operational return, not yet a canonical pair loader. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchShiftReturn

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (push flipped)
open Shared.Beeping.NPcoNP.Source284ScratchShift (written scratchPrefix)

/-- One entry state skips the final zero written by the shifter; the
continuation is the existing reverse scanner starting at its marker state. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 4⟩
  else shiftRow 1 (Source284ScratchFlipReturn.table continuation (q-1) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (7+states) (table continuation) := by
  have hc := Source284ScratchFlipReturn.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [table] at hnext; omega
  · have ht : (shiftRow 1 (Source284ScratchFlipReturn.table continuation (q-1) b)).next = some q' := by
      simpa [table,h0] using hnext
    have hq0 : q-1 < 6+states := by omega
    cases he : (Source284ScratchFlipReturn.table continuation (q-1) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hc (q-1) hq0 b r he
      simp [shiftRow,he] at ht
      subst q'
      omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (1+q) b = shiftRow 1 (Source284ScratchFlipReturn.table continuation q b) := by
  simp [table]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 1 c) =
      shiftConfig 1 (step (Source284ScratchFlipReturn.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 1 c) clock =
      shiftConfig 1 (run (Source284ScratchFlipReturn.table continuation) c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

/-- The reverse representation written by the shifter has a known `0`
followed by the marker-delimited reversed stream. -/
theorem fold_scratchPrefix (left : Nat) (w : List Bool) :
    payloadFold left (scratchPrefix w) = 2*push left w := by
  induction w generalizing left with
  | nil => simp [scratchPrefix,payloadFold,push]
  | cons b bs ih =>
    have h := ih (4*left+2*bit b+1)
    cases b <;> simpa [scratchPrefix,payloadFold,push,bit,Nat.mul_add,← Nat.mul_assoc,Nat.add_assoc] using h

theorem fold_written (certificate : Nat) (w : List Bool) :
    payloadFold (2*certificate) (written false w) = 2*push (4*certificate) w := by
  rw [Source284ScratchShift.written_eq]
  have he : 2*(2*certificate) = 4*certificate := by omega
  simpa [payloadFold,he] using fold_scratchPrefix (4*certificate) w

theorem entry_step (continuation : Nat → Bool → Row) (left right : Nat) :
    step (table continuation) ⟨left,2*right,some 0⟩ = ⟨2*left,right,some 4⟩ := by
  simp [step,table,bit,Nat.testBit_zero]

/-- The return follows the stream's markers and does not use its length as
runtime data. The original certificate remains intact, with one zero cell
between it and the returned head; one high suffix bit was overwritten. -/
theorem return_frame (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (table continuation)
      ⟨2*(tail/2),payloadFold (2*certificate) (written false w),some 0⟩ (2*w.length+3) =
      ⟨2*certificate,2*flipped w (tail/2),some 7⟩ := by
  rw [fold_written]
  have ht : 2*w.length+3 = 1+(2*w.length+2) := by omega
  rw [ht,Source284PayloadPop.run_add]
  change run (table continuation)
    (step (table continuation) ⟨2*(tail/2),2*push (4*certificate) w,some 0⟩) _ = _
  rw [entry_step]
  have he : 2*(2*(tail/2)) = 4*(tail/2) := by omega
  rw [he]
  change run (table continuation)
    (shiftConfig 1 ⟨4*(tail/2),push (4*certificate) w,some 3⟩) _ = _
  rw [relocated_run]
  have hclock : 2*w.length+2 = (2*w.length)+2 := by omega
  rw [hclock,Source284ScratchFlipReturn.run_add,Source284ScratchFlipReturn.reverse_pairs,
    Source284ScratchFlipReturn.raw_flipped]
  have hfinish := Source284ScratchFlipReturn.finish continuation (flipped w (tail/2)) (2*certificate)
  have hec : 2*(2*certificate) = 4*certificate := by omega
  rw [hec] at hfinish
  rw [hfinish]
  rfl

end Shared.Beeping.NPcoNP.Source284ScratchShiftReturn
