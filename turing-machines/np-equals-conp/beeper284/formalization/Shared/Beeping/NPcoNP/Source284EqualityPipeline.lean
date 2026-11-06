import Shared.Beeping.NPcoNP.Source284RetryInitPipeline
import Shared.Beeping.NPcoNP.Source284EqualityDispatch

/-! Source program which constructs a payload-length unary tape, detects
matching lengths, rewinds the paid equality dispatch and resets both tracks.
It does not yet encode a canonical verifier pair. -/
set_option maxRecDepth 2048
namespace Shared.Beeping.NPcoNP.Source284EqualityPipeline

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284RetryInitPipeline.description (23+states) (Source284EqualityDispatch.table continuation)

def totalCost (n : Nat) : Nat := Source284RetryInitPipeline.totalCost n+(8*n+21)

def finalTail (n suffix : Nat) : Nat := (((((suffix/4)/4)/2)/2)/4^n)

/-- One source program produces the prepared unary/payload tape from a
framed input, with the certificate and high suffix precisely tracked. -/
theorem source_pipeline (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost w.length) =
    ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) (finalTail w.length suffix),active 303⟩ := by
  have hc := Source284EqualityDispatch.closed states continuation hn hv
  have hp := Source284RetryInitPipeline.source_pipeline (23+states)
    (Source284EqualityDispatch.table continuation) w certificate suffix (by omega) hc
  have hr := Source284RetryInitPipeline.source_after (23+states)
    (Source284EqualityDispatch.table continuation) 1
    (2*pairTape (List.replicate w.length true) certificate)
    (zeros w (flipped [false] (finalTail w.length suffix))) (8*w.length+21) (by omega) (by omega) hc
  unfold totalCost
  rw [Source284Relative.run_add_clock]
  change Source284Relative.run (description states continuation)
    (Source284Relative.run (Source284RetryInitPipeline.description (23+states)
      (Source284EqualityDispatch.table continuation)) _ _) _ = _
  rw [hp]
  change Source284Relative.run (description states continuation)
    ⟨2*pairTape (List.replicate w.length true) certificate,
      zeros w (flipped [false] (finalTail w.length suffix)),active (280+1)⟩ _ = _
  change Source284Relative.run (description states continuation) _ _ = _ at hr
  rw [hr,Source284EqualityDispatch.reset_equal]
  simp [description,shiftConfig,toSource,nextState,active,Nat.add_assoc]

theorem totalCost_le (n : Nat) : totalCost n ≤ 4*n*n*n+42*n*n+118*n+96 := by
  have h := Source284RetryInitPipeline.totalCost_le n
  unfold totalCost
  have he : (4*n*n*n+42*n*n+110*n+75)+(8*n+21) =
      4*n*n*n+42*n*n+118*n+96 := by ring
  omega

/-- At the prepared-tape state the caller's finite continuation executes in
the same source table, with every relocation recorded. -/
theorem source_after (states : Nat) (continuation : Nat → Bool → Row) (mode : Nat)
    (left right fuel : Nat) (hn : 0 < states) (hm : mode < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) ⟨left,right,active (303+mode)⟩ fuel =
    toSource (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
      (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6 (shiftConfig 14 (shiftConfig 14
        (shiftConfig 97 (shiftConfig 2 (shiftConfig 3 (shiftConfig 7 (shiftConfig 5 (shiftConfig 6
          (run continuation ⟨left,right,some mode⟩ fuel)))))))))))))))))) := by
  have hc := Source284EqualityDispatch.closed states continuation hn hv
  have hr := Source284RetryInitPipeline.source_after (23+states)
    (Source284EqualityDispatch.table continuation) (23+mode) left right fuel (by omega) (by omega) hc
  have he : 280+(23+mode) = 303+mode := by omega
  rw [he] at hr
  change Source284Relative.run (description states continuation) _ _ = _ at hr
  rw [Source284EqualityDispatch.continuation_run] at hr
  exact hr

/-- The parser covers every numeric input and the same cubic bound holds
without a supplied length, witness, counter or high-suffix assumption. -/
theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix t : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      t ≤ 4*(Source284Parser.length input)^3+42*(Source284Parser.length input)^2+
        118*(Source284Parser.length input)+96 ∧
      Source284Relative.run (description states continuation) (Source284Relative.initial input certificate) t =
    ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) (finalTail w.length suffix),active 303⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,totalCost (Source284Parser.length input),hw,hlen.symm,?_,?_⟩
  · have h := totalCost_le (Source284Parser.length input)
    nlinarith
  · rw [hlen,← hw]
    exact source_pipeline states continuation w certificate suffix hn hv

namespace Fixtures
example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 0 7) 96 =
      ⟨30,4,active 303⟩ := by
  simpa [encodeFrame,totalCost,finalTail,Source284RetryInitPipeline.totalCost,
    Source284PayloadSentinelPipeline.totalCost_formula,Source284RetryLoopComplete.totalCost,
    Source284RetryLoopComplete.retriesCost,Source284OneRetry.cost,pairTape,
    Source284PayloadLoop.scratch,flipped,bit] using source_pipeline states continuation [] 7 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 3 7) 232 =
      ⟨120,22,active 303⟩ := by
  simpa [encodeFrame,totalCost,finalTail,Source284RetryInitPipeline.totalCost,
    Source284PayloadSentinelPipeline.totalCost_formula,Source284RetryLoopComplete.totalCost,
    Source284RetryLoopComplete.retriesCost,Source284OneRetry.cost,pairTape,
    Source284PayloadLoop.scratch,flipped,bit] using source_pipeline states continuation [true] 7 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 295 7) 432 =
      ⟨480,86,active 303⟩ := by
  simpa [encodeFrame,totalCost,finalTail,Source284RetryInitPipeline.totalCost,
    Source284PayloadSentinelPipeline.totalCost_formula,Source284RetryLoopComplete.totalCost,
    Source284RetryLoopComplete.retriesCost,Source284OneRetry.cost,pairTape,
    Source284PayloadLoop.scratch,flipped,bit] using source_pipeline states continuation [true,false] 7 9 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 32775 7) 432 =
      ⟨480,598,active 303⟩ := by
  simpa [encodeFrame,totalCost,finalTail,Source284RetryInitPipeline.totalCost,
    Source284PayloadSentinelPipeline.totalCost_formula,Source284RetryLoopComplete.totalCost,
    Source284RetryLoopComplete.retriesCost,Source284OneRetry.cost,pairTape,
    Source284PayloadLoop.scratch,flipped,bit] using source_pipeline states continuation [true,false] 7 1024 hn hv
end Fixtures

end Shared.Beeping.NPcoNP.Source284EqualityPipeline
