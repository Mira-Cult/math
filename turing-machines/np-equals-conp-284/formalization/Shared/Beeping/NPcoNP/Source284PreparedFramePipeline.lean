import Shared.Beeping.NPcoNP.Source284EqualityPipeline
import Shared.Beeping.NPcoNP.Source284PrepareFrame
import Shared.Beeping.NPcoNP.Source284NormalizedWindow

/-! One finite source program produces the canonical input frame together
with the unmarked unary side and retained certificate. The witness is not
yet packed into the canonical verifier pair. -/
set_option maxRecDepth 2048
namespace Shared.Beeping.NPcoNP.Source284PreparedFramePipeline

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284RawParse (payload)

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284EqualityPipeline.description (80+states) (Source284PrepareFrame.table continuation)

def totalCost (n : Nat) : Nat := Source284EqualityPipeline.totalCost n+(10*n+21)

theorem source_prepare (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (left tail : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      ⟨left,2*flipped (w++[false]) tail,active 303⟩ (10*w.length+21) =
      ⟨2*left,encodeFrame w (8*tail+1),active 383⟩ := by
  have hc := Source284PrepareFrame.closed states continuation hn hv
  have hr := Source284EqualityPipeline.source_after (80+states) (Source284PrepareFrame.table continuation)
    0 left (2*flipped (w++[false]) tail) (10*w.length+21) (by omega) (by omega) hc
  change Source284Relative.run (description states continuation)
    ⟨left,2*flipped (w++[false]) tail,active (303+0)⟩ _ = _ at hr
  rw [Source284PrepareFrame.prepare] at hr
  simpa [description,shiftConfig,toSource,nextState,active,← Nat.add_assoc] using hr

/-- The original input and certificate reach a canonical input frame with
exactly as many unmarked unary pairs as payload bits, all in one source table. -/
theorem source_pipeline (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost w.length) =
    ⟨2*pairTape (List.replicate w.length false) certificate,
      encodeFrame w (8*Source284EqualityPipeline.finalTail w.length suffix+1),active 383⟩ := by
  have hc := Source284PrepareFrame.closed states continuation hn hv
  have hp := Source284EqualityPipeline.source_pipeline (80+states) (Source284PrepareFrame.table continuation)
    w certificate suffix (by omega) hc
  unfold totalCost
  rw [Source284Relative.run_add_clock]
  change Source284Relative.run (description states continuation)
    (Source284Relative.run (Source284EqualityPipeline.description (80+states)
      (Source284PrepareFrame.table continuation)) _ _) _ = _
  rw [hp,source_prepare states continuation w (pairTape (List.replicate w.length false) certificate)
    (Source284EqualityPipeline.finalTail w.length suffix) hn hv]

theorem totalCost_le (n : Nat) : totalCost n ≤ 4*n*n*n+42*n*n+128*n+117 := by
  have h := Source284EqualityPipeline.totalCost_le n
  unfold totalCost
  have he : (4*n*n*n+42*n*n+118*n+96)+(10*n+21) =
      4*n*n*n+42*n*n+128*n+117 := by ring
  omega

/-- The supplied continuation runs after the frame conversion in the same
encoded source table. -/
theorem source_after (states : Nat) (continuation : Nat → Bool → Row) (mode : Nat)
    (left right fuel : Nat) (hn : 0 < states) (hm : mode < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) ⟨left,right,active (383+mode)⟩ fuel =
    toSource (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
      (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6 (shiftConfig 14 (shiftConfig 14
        (shiftConfig 97 (shiftConfig 2 (shiftConfig 3 (shiftConfig 7 (shiftConfig 5 (shiftConfig 6
          (shiftConfig 6 (shiftConfig 6 (shiftConfig 36 (shiftConfig 32
            (run continuation ⟨left,right,some mode⟩ fuel)))))))))))))))))))))) := by
  have hc := Source284PrepareFrame.closed states continuation hn hv
  have hr := Source284EqualityPipeline.source_after (80+states) (Source284PrepareFrame.table continuation)
    (80+mode) left right fuel (by omega) (by omega) hc
  have he : 303+(80+mode) = 383+mode := by omega
  rw [he] at hr
  change Source284Relative.run (description states continuation) _ _ = _ at hr
  rw [Source284PrepareFrame.continuation_run] at hr
  exact hr

/-- Every numeric input reaches the prepared frame and unary side within the
same cubic bound; ignored high suffix bits remain explicitly represented. -/
theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix t : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      t ≤ 4*(Source284Parser.length input)^3+42*(Source284Parser.length input)^2+
        128*(Source284Parser.length input)+117 ∧
      Source284Relative.run (description states continuation) (Source284Relative.initial input certificate) t =
    ⟨2*pairTape (List.replicate w.length false) certificate,
      encodeFrame w (8*Source284EqualityPipeline.finalTail w.length suffix+1),active 383⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,totalCost (Source284Parser.length input),hw,hlen.symm,?_,?_⟩
  · have h := totalCost_le (Source284Parser.length input)
    nlinarith
  · rw [hlen,← hw]
    exact source_pipeline states continuation w certificate suffix hn hv

/-- The verifier's canonical input bits appear in the exact low window of the
actual resulting source tape. The unary tokens and certificate remain on the
other half; this does not yet pack a witness into the pair. -/
theorem source_canonical_window (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (right t : Nat),
      t ≤ 4*(Source284Parser.length input)^3+42*(Source284Parser.length input)^2+
        128*(Source284Parser.length input)+117 ∧
      Source284Relative.run (description states continuation) (Source284Relative.initial input certificate) t =
        ⟨2*pairTape (List.replicate (Source284Parser.length input) false) certificate,right,active 383⟩ ∧
      right % 2^(Source284PackedGuardWindow.inputBits input.bits).length =
        value (Source284PackedGuardWindow.inputBits input.bits) := by
  obtain ⟨w,suffix,t,hw,hlen,hcost,hr⟩ := source_total_progress states continuation input certificate hn hv
  have hp : payload input.bits = w := by
    rw [← hw]
    exact Source284NormalizedWindow.payload_encodeFrame w suffix
  refine ⟨encodeFrame w (8*Source284EqualityPipeline.finalTail w.length suffix+1),t,hcost,?_,?_⟩
  · simpa [hlen] using hr
  · have hmod := Source284NormalizedWindow.normalized_mod w (4*Source284EqualityPipeline.finalTail w.length suffix)
    have ht : 2*(4*Source284EqualityPipeline.finalTail w.length suffix)+1 =
        8*Source284EqualityPipeline.finalTail w.length suffix+1 := by omega
    rw [ht] at hmod
    have hval : value (Source284PackedGuardWindow.inputBits input.bits) = encodeFrame w 1 := by
      rw [Source284NormalizedWindow.canonical_input_value,hp]
    rw [hval]
    have hl := Source284PackedGuardWindow.inputBits_length input.bits
    rw [Shared.Codes.BinaryAdditionCanonical.value_bits] at hl
    rw [hl,← hlen]
    have he : 2^(2*w.length+2) = 4^(w.length+1) := by
      have h' : 2*w.length+2 = 2*(w.length+1) := by omega
      rw [h',Nat.pow_mul]
    rw [he]
    exact hmod

/-- A bounded bit reader sees exactly the existing verifier's canonical
input list, with no dependence on the retained high suffix. -/
theorem source_canonical_window_bits (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (right t : Nat),
      t ≤ 4*(Source284Parser.length input)^3+42*(Source284Parser.length input)^2+
        128*(Source284Parser.length input)+117 ∧
      Source284Relative.run (description states continuation) (Source284Relative.initial input certificate) t =
        ⟨2*pairTape (List.replicate (Source284Parser.length input) false) certificate,right,active 383⟩ ∧
      Source284CanonicalPairWindow.window (Source284PackedGuardWindow.inputBits input.bits).length right =
        Source284PackedGuardWindow.inputBits input.bits := by
  obtain ⟨right,t,hcost,hr,hw⟩ := source_canonical_window states continuation input certificate hn hv
  refine ⟨right,t,hcost,hr,?_⟩
  apply Source284CanonicalPairWindow.same_length_value_injective
  · exact Source284CanonicalPairWindow.window_length _ _
  · rw [Source284CanonicalPairWindow.window_value,hw]

namespace Fixtures
example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 0 7) 117 =
      ⟨60,2,active 383⟩ := by
  simpa [encodeFrame,totalCost,Source284EqualityPipeline.totalCost,Source284EqualityPipeline.finalTail,
    Source284RetryInitPipeline.totalCost,Source284PayloadSentinelPipeline.totalCost_formula,
    Source284RetryLoopComplete.totalCost,Source284RetryLoopComplete.retriesCost,Source284OneRetry.cost,
    pairTape,Source284PayloadLoop.scratch,flipped,bit] using source_pipeline states continuation [] 7 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 3 7) 263 =
      ⟨240,11,active 383⟩ := by
  simpa [encodeFrame,totalCost,Source284EqualityPipeline.totalCost,Source284EqualityPipeline.finalTail,
    Source284RetryInitPipeline.totalCost,Source284PayloadSentinelPipeline.totalCost_formula,
    Source284RetryLoopComplete.totalCost,Source284RetryLoopComplete.retriesCost,Source284OneRetry.cost,
    pairTape,Source284PayloadLoop.scratch,flipped,bit] using source_pipeline states continuation [true] 7 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 295 7) 473 =
      ⟨960,39,active 383⟩ := by
  simpa [encodeFrame,totalCost,Source284EqualityPipeline.totalCost,Source284EqualityPipeline.finalTail,
    Source284RetryInitPipeline.totalCost,Source284PayloadSentinelPipeline.totalCost_formula,
    Source284RetryLoopComplete.totalCost,Source284RetryLoopComplete.retriesCost,Source284OneRetry.cost,
    pairTape,Source284PayloadLoop.scratch,flipped,bit] using source_pipeline states continuation [true,false] 7 9 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 32775 7) 473 =
      ⟨960,295,active 383⟩ := by
  simpa [encodeFrame,totalCost,Source284EqualityPipeline.totalCost,Source284EqualityPipeline.finalTail,
    Source284RetryInitPipeline.totalCost,Source284PayloadSentinelPipeline.totalCost_formula,
    Source284RetryLoopComplete.totalCost,Source284RetryLoopComplete.retriesCost,Source284OneRetry.cost,
    pairTape,Source284PayloadLoop.scratch,flipped,bit] using source_pipeline states continuation [true,false] 7 1024 hn hv
end Fixtures

end Shared.Beeping.NPcoNP.Source284PreparedFramePipeline
