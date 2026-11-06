import Shared.Beeping.NPcoNP.Source284ScratchSentinel
import Shared.Beeping.NPcoNP.Source284ScratchLoopPipeline

/-! Actual finite source-table initialization of a certificate sentinel and
an unbounded loop producing two zero cells per pair of shift cycles. The
number `k` in the theorems is a time index, not a machine-side stop command. -/
set_option maxRecDepth 2048

namespace Shared.Beeping.NPcoNP.Source284ScratchUnaryRunway

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284ScratchSentinel (unaryPairs)

def setup (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchSentinel.special (Source284ScratchShiftCycle.table continuation)

theorem setup_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (28+states) (setup continuation) := by
  have hc := Source284ScratchShiftCycle.closed states continuation hn hv
  have hs := Source284ScratchSentinel.closed (14+states)
    (Source284ScratchShiftCycle.table continuation) (by omega) hc
  have he : 14+(14+states) = 28+states := by omega
  rw [he] at hs
  exact hs

/-- Two paid shifts create the low-first `0,1` boundary immediately above
the untouched certificate. -/
theorem setup_frame (continuation : Nat → Bool → Row) (w : List Bool) (certificate tail : Nat) :
    run (setup continuation) ⟨certificate,2*flipped w tail,some 0⟩ (2*(4*w.length+7)) =
      ⟨4*certificate+2,2*flipped w ((tail/2)/2),some 28⟩ := by
  have ht : 2*(4*w.length+7) = (4*w.length+7)+(4*w.length+7) := by ring
  rw [ht,Source284PayloadPop.run_add]
  change run (Source284ScratchSentinel.special (Source284ScratchShiftCycle.table continuation))
    (run (Source284ScratchSentinel.special (Source284ScratchShiftCycle.table continuation)) _ _) _ = _
  rw [Source284ScratchSentinel.special_frame]
  change run (Source284ScratchSentinel.special (Source284ScratchShiftCycle.table continuation))
    (shiftConfig 14 ⟨2*certificate+1,2*flipped w (tail/2),some 0⟩) _ = _
  rw [Source284ScratchSentinel.continuation_run,Source284ScratchShiftCycle.cycle_frame]
  simp [shiftConfig]
  omega

/-- A pair of actual loop cycles creates one additional two-cell zero token.
The loop itself has no stopping rule; `k` is the proof's time index. -/
theorem runway (k : Nat) (w : List Bool) (certificate tail : Nat) :
    run (setup Source284ScratchShiftLoop.table) ⟨certificate,2*flipped w tail,some 0⟩
      ((2+2*k)*(4*w.length+7)) =
      ⟨Source284LoaderAlgebra.stack (unaryPairs k) certificate,
        2*flipped w (((tail/2)/2)/2^(2*k)),some 28⟩ := by
  have ht : (2+2*k)*(4*w.length+7) = 2*(4*w.length+7)+(2*k)*(4*w.length+7) := by ring
  rw [ht,Source284PayloadPop.run_add,setup_frame]
  change run (Source284ScratchSentinel.special
      (Source284ScratchShiftCycle.table Source284ScratchShiftLoop.table))
    (shiftConfig 14 (shiftConfig 14 ⟨4*certificate+2,2*flipped w ((tail/2)/2),some 0⟩)) _ = _
  rw [Source284ScratchSentinel.continuation_run,Source284ScratchShiftCycle.relocated_run,
    Source284ScratchShiftLoop.iterations,← Source284ScratchSentinel.unaryPairs_stack]
  rfl

def description : Nat :=
  Source284ScratchFlipPipeline.description 42 (setup Source284ScratchShiftLoop.table)

def elapsed (k n : Nat) : Nat :=
  Source284ScratchFlipPipeline.totalCost n+(2+2*k)*(4*n+7)

/-- One encoded source program constructs the sentinel and reaches every
finite unary-runway prefix; no external length or interpreter is supplied. -/
theorem source_runway (k : Nat) (w : List Bool) (certificate suffix : Nat) :
    Source284Relative.run description (Source284Relative.initial (encodeFrame w suffix) certificate)
      (elapsed k w.length) =
      ⟨Source284LoaderAlgebra.stack (unaryPairs k) certificate,
        2*flipped w ((((suffix/4)/2)/2)/2^(2*k)),active 170⟩ := by
  let c : Config := ⟨certificate,2*flipped w (suffix/4),some 0⟩
  have hc := setup_closed 14 Source284ScratchShiftLoop.table (by decide) Source284ScratchShiftLoop.closed
  have hvalid : Valid (142+42)
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 c))))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := Source284ScratchNormalizePipeline.source_continuation_run 42
    (setup Source284ScratchShiftLoop.table) c ((2+2*k)*(4*w.length+7)) (by decide) hc hvalid
  dsimp only [c] at hr
  rw [runway] at hr
  have hp : Source284Relative.run description
      (Source284Relative.initial (encodeFrame w suffix) certificate)
      (Source284ScratchFlipPipeline.totalCost w.length) =
      ⟨certificate,2*flipped w (suffix/4),active 142⟩ := by
    exact Source284ScratchFlipPipeline.source_pipeline 42 (setup Source284ScratchShiftLoop.table)
      w certificate suffix (by decide) hc
  unfold elapsed
  rw [Source284Relative.run_add_clock,hp]
  simpa [description,shiftConfig,toSource,nextState,active,Nat.add_assoc] using hr

/-- At a quadratic time indexed by the payload length, the tape contains
exactly that many unary zero pairs before the sentinel. The source program
continues looping; it does not autonomously detect or stop at this time. -/
theorem source_payload_length_prefix (w : List Bool) (certificate suffix : Nat) :
    Source284Relative.run description (Source284Relative.initial (encodeFrame w suffix) certificate)
      (10*w.length*w.length+44*w.length+38) =
      ⟨Source284LoaderAlgebra.stack (unaryPairs w.length) certificate,
        2*flipped w ((((suffix/4)/2)/2)/2^(2*w.length)),active 170⟩ := by
  have h := source_runway w.length w certificate suffix
  have ht : elapsed w.length w.length = 10*w.length*w.length+44*w.length+38 := by
    rw [elapsed,Source284ScratchFlipPipeline.totalCost_formula]
    ring
  rw [ht] at h
  exact h

/-- This finite-prefix result applies to every numeric input, including the
empty input. It does not assert that the program stops at this prefix. -/
theorem source_all_inputs_prefix (input certificate : Nat) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run description (Source284Relative.initial input certificate)
        (10*(Source284Parser.length input)*(Source284Parser.length input)+
          44*(Source284Parser.length input)+38) =
      ⟨Source284LoaderAlgebra.stack (unaryPairs (Source284Parser.length input)) certificate,
        2*flipped w ((((suffix/4)/2)/2)/2^(2*(Source284Parser.length input))),active 170⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [hlen,← hw]
  exact source_payload_length_prefix w certificate suffix

namespace Fixtures
example : Source284Relative.run description (Source284Relative.initial 0 7) 38 =
    ⟨30,0,active 170⟩ := by
  simpa [encodeFrame,unaryPairs,Source284LoaderAlgebra.stack,flipped] using
    source_payload_length_prefix [] 7 0

example : Source284Relative.run description (Source284Relative.initial 1 7) 92 =
    ⟨120,4,active 170⟩ := by
  simpa [encodeFrame,unaryPairs,Source284LoaderAlgebra.stack,flipped,bit] using
    source_payload_length_prefix [false] 7 0

example : Source284Relative.run description (Source284Relative.initial 295 7) 166 =
    ⟨480,22,active 170⟩ := by
  simpa [encodeFrame,unaryPairs,Source284LoaderAlgebra.stack,flipped,bit] using
    source_payload_length_prefix [true,false] 7 9
end Fixtures

end Shared.Beeping.NPcoNP.Source284ScratchUnaryRunway
