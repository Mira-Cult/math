import Shared.Beeping.NPcoNP.Source284ScratchShift
import Shared.Beeping.NPcoNP.Source284ScratchNormalizePipeline
import Shared.Beeping.NPcoNP.Source284LoaderAlgebra

/-! Connect the finite shift primitive to the actual encoded scratch source
pipeline. The shifted bits and original certificate occupy one tape half;
recoverability below is arithmetic and is not a source-machine return. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchShiftPipeline

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame payloadFold)
open Shared.Beeping.NPcoNP.Source284ScratchShift (written)

/-- Cross the already-proved zero boundary, then run the finite shifter. -/
def entry (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 1⟩
  else shiftRow 1 (Source284ScratchShift.table continuation (q-1) b)

theorem entry_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (7+states) (entry continuation) := by
  have hc := Source284ScratchShift.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [entry] at hnext; omega
  · have ht : (shiftRow 1 (Source284ScratchShift.table continuation (q-1) b)).next = some q' := by
      simpa [entry,h0] using hnext
    have hq0 : q-1 < 6+states := by omega
    cases he : (Source284ScratchShift.table continuation (q-1) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hc (q-1) hq0 b r he
      simp [shiftRow,he] at ht
      subst q'
      omega

theorem entry_step (continuation : Nat → Bool → Row) (left right : Nat) :
    step (entry continuation) ⟨left,2*right,some 0⟩ = ⟨2*left,right,some 1⟩ := by
  simp [step,entry,bit,Nat.testBit_zero]

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    entry continuation (1+q) b = shiftRow 1 (Source284ScratchShift.table continuation q b) := by
  simp [entry]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (entry continuation) (shiftConfig 1 c) =
      shiftConfig 1 (step (Source284ScratchShift.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (entry continuation) (shiftConfig 1 c) clock =
      shiftConfig 1 (run (Source284ScratchShift.table continuation) c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

theorem shift_entry (continuation : Nat → Bool → Row) (w : List Bool) (certificate tail : Nat) :
    run (entry continuation) ⟨certificate,2*flipped w tail,some 0⟩ (2*w.length+4) =
      ⟨2*(tail/2),payloadFold (2*certificate) (written false w),some 7⟩ := by
  have ht : 2*w.length+4 = (2*w.length+3)+1 := by omega
  rw [ht,Source284HardwireTable.run_front,entry_step]
  change run (entry continuation) (shiftConfig 1 ⟨2*certificate,flipped w tail,some 0⟩) _ = _
  rw [relocated_run,Source284ScratchShift.shift]
  rfl

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchFlipPipeline.table (entry continuation)

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284ScratchFlipPipeline.description (7+states) (entry continuation)

def totalCost (n : Nat) : Nat := Source284ScratchFlipPipeline.totalCost n + (2*n+4)

theorem totalCost_formula (n : Nat) : totalCost n = 2*n*n+24*n+28 := by
  rw [totalCost,Source284ScratchFlipPipeline.totalCost_formula]
  ring

/-- The source encoding performs the shifted-stream pass after the earlier
pipeline, and all head turns and state relocations are charged. -/
theorem source_shift (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate tail : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      ⟨certificate,2*flipped w tail,active 142⟩ (2*w.length+4) =
      ⟨2*(tail/2),payloadFold (2*certificate) (written false w),active 149⟩ := by
  let c : Config := ⟨certificate,2*flipped w tail,some 0⟩
  have hc : Closed (7+states) (entry continuation) := entry_closed states continuation hn hv
  have hvalid : Valid (142+(7+states))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 c))))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := Source284ScratchNormalizePipeline.source_continuation_run (7+states) (entry continuation)
    c (2*w.length+4) (by omega) hc hvalid
  dsimp only [c] at hr
  rw [shift_entry] at hr
  simpa [description,shiftConfig,toSource,nextState,active,Nat.add_assoc] using hr

/-- From the original numeric frame, the paid source program constructs the
scratch stream and inserts one low cell. Three ignored high suffix bits have
been used in total; the rest remains on the other side of the head. -/
theorem source_pipeline (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost w.length) =
      ⟨2*((suffix/4)/2),payloadFold (2*certificate) (written false w),active 149⟩ := by
  have hc := entry_closed states continuation hn hv
  unfold totalCost description
  rw [Source284Relative.run_add_clock,
    Source284ScratchFlipPipeline.source_pipeline (7+states) (entry continuation)
      w certificate suffix (by omega) hc]
  change Source284Relative.run (description states continuation) _ _ = _
  rw [source_shift states continuation w certificate (suffix/4) hn hv]

/-- Any supplied finite continuation runs after the complete shift, with
both the source prefix and continuation steps charged. -/
theorem source_after_pipeline (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix clock : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    let c : Config := ⟨2*((suffix/4)/2),payloadFold (2*certificate) (written false w),some 0⟩
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost w.length+clock) =
      toSource (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 (shiftConfig 1 (shiftConfig 6
          (run continuation c clock)))))))))) := by
  let c : Config := ⟨2*((suffix/4)/2),payloadFold (2*certificate) (written false w),some 0⟩
  have hc : Closed (7+states) (entry continuation) := entry_closed states continuation hn hv
  have hvalid : Valid (142+(7+states))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 (shiftConfig 1 (shiftConfig 6 c))))))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := Source284ScratchNormalizePipeline.source_continuation_run (7+states) (entry continuation)
    (shiftConfig 1 (shiftConfig 6 c)) clock (by omega) hc hvalid
  change Source284Relative.run (description states continuation)
      ⟨2*((suffix/4)/2),payloadFold (2*certificate) (written false w),active 149⟩ clock = _ at hr
  rw [relocated_run,Source284ScratchShift.relocated_run] at hr
  rw [Source284Relative.run_add_clock,source_pipeline states continuation w certificate suffix hn hv]
  exact hr

/-- The output still contains the entire certificate beyond the written
stream. `transfer` is an arithmetic inverse, not an implemented tape return. -/
theorem data_recoverable (w : List Bool) (certificate : Nat) :
    Source284LoaderAlgebra.transfer (written false w).length 0
      (payloadFold (2*certificate) (written false w)) =
        (Shared.Codes.BitNumeralCompare.value (written false w),2*certificate) :=
  Source284LoaderAlgebra.push_transfer (written false w) (2*certificate)

/-- Every numeric input, including virtual-zero and empty prefixes, reaches
the continuation. No runtime input length is assumed by the table. -/
theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description states continuation)
        (Source284Relative.initial input certificate) (totalCost (Source284Parser.length input)) =
        ⟨2*((suffix/4)/2),payloadFold (2*certificate) (written false w),active 149⟩ ∧
      Source284LoaderAlgebra.transfer (written false w).length 0
        (payloadFold (2*certificate) (written false w)) =
          (Shared.Codes.BitNumeralCompare.value (written false w),2*certificate) := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_,data_recoverable w certificate⟩
  rw [hlen,← hw]
  exact source_pipeline states continuation w certificate suffix hn hv

namespace Fixtures

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial 0 7) 28 = ⟨0,56,active 149⟩ := by
  simpa [encodeFrame,totalCost_formula,written,payloadFold] using
    source_pipeline states continuation [] 7 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial 295 7) 84 = ⟨2,922,active 149⟩ := by
  simpa [encodeFrame,totalCost_formula,written,payloadFold] using
    source_pipeline states continuation [true,false] 7 9 hn hv

end Fixtures

end Shared.Beeping.NPcoNP.Source284ScratchShiftPipeline
