import Shared.Beeping.NPcoNP.Source284RetryLoopSource
import Shared.Beeping.NPcoNP.Source284ScratchUnaryRunway
import Shared.Beeping.NPcoNP.Source284PayloadSentinelPipeline

/-! One numeric source program initializes the payload and zero-token
sentinels, then runs the autonomous retry loop to equality. This is an
input-dependent finite preprocessing program, not yet a verifier-pair
loader or a physical beeping-machine refinement. -/
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
namespace Shared.Beeping.NPcoNP.Source284RetryInitPipeline

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

def setup (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchUnaryRunway.setup (Source284RetryLoop.table continuation)

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284PayloadSentinelPipeline.description (28+(97+states)) (setup continuation)

def totalCost (n : Nat) : Nat :=
  Source284PayloadSentinelPipeline.totalCost n + 2*(4*(n+1)+7) +
    Source284RetryLoopComplete.totalCost 0 n

theorem setup_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 2 ≤ states) (hv : Closed states continuation) : Closed (28+(97+states)) (setup continuation) := by
  have hr := Source284RetryLoop.closed states continuation hn hv
  exact Source284ScratchUnaryRunway.setup_closed (97+states) (Source284RetryLoop.table continuation) (by omega) hr

/-- Construct the protected empty unary side after the payload sentinel. -/
theorem source_setup (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate tail : Nat) (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      ⟨certificate,2*flipped w tail,active 155⟩ (2*(4*w.length+7)) =
      ⟨4*certificate+2,2*flipped w ((tail/2)/2),active 183⟩ := by
  let c : Config := ⟨certificate,2*flipped w tail,some 0⟩
  have hc := setup_closed states continuation hn hv
  have hs := Source284PayloadSentinel.closed (28+(97+states)) (setup continuation) (by omega) hc
  have hvalid : Valid (142+(13+(28+(97+states))))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6 c))))))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := Source284ScratchNormalizePipeline.source_continuation_run (13+(28+(97+states)))
    (Source284PayloadSentinel.table (setup continuation)) (shiftConfig 7 (shiftConfig 6 c))
    (2*(4*w.length+7)) (by omega) hs hvalid
  rw [Source284PayloadSentinel.relocated_run,Source284ScratchFlipReturn.relocated_run] at hr
  dsimp only [c] at hr
  unfold setup at hr
  rw [Source284ScratchUnaryRunway.setup_frame] at hr
  simpa [description,setup,Source284PayloadSentinelPipeline.description,shiftConfig,toSource,nextState,
    active,Nat.add_assoc] using hr

/-- From that actual setup state the retry loop finishes, starting at zero
unary tokens and charging every comparison, reset and growth step. -/
theorem source_loop (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate tail : Nat) (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      ⟨4*certificate+2,2*flipped (w++[false]) tail,active 183⟩
      (Source284RetryLoopComplete.totalCost 0 w.length) =
    ⟨2*pairTape (List.replicate w.length true) certificate,
      zeros w (flipped [false] (tail/4^w.length)),active 281⟩ := by
  let c : Config := ⟨pairTape (List.replicate 0 false) certificate,2*flipped (w++[false]) tail,some 0⟩
  have hc := setup_closed states continuation hn hv
  have hs := Source284PayloadSentinel.closed (28+(97+states)) (setup continuation) (by omega) hc
  have hvalid : Valid (142+(13+(28+(97+states))))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6
          (shiftConfig 14 (shiftConfig 14 c))))))))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := Source284ScratchNormalizePipeline.source_continuation_run (13+(28+(97+states)))
    (Source284PayloadSentinel.table (setup continuation))
    (shiftConfig 7 (shiftConfig 6 (shiftConfig 14 (shiftConfig 14 c))))
    (Source284RetryLoopComplete.totalCost 0 w.length) (by omega) hs hvalid
  rw [Source284PayloadSentinel.relocated_run,Source284ScratchFlipReturn.relocated_run] at hr
  change Source284Relative.run _ _ _ = toSource (shiftConfig 8 (shiftConfig 8 (shiftConfig 16
    (shiftConfig 32 (shiftConfig 69 (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6
      (run (Source284ScratchSentinel.special (Source284ScratchShiftCycle.table (Source284RetryLoop.table continuation)))
        (shiftConfig 14 (shiftConfig 14 c)) _)))))))))) at hr
  rw [Source284ScratchSentinel.continuation_run,Source284ScratchShiftCycle.relocated_run] at hr
  dsimp only [c] at hr
  rw [Source284RetryLoopComplete.complete _ 0 w certificate tail (by omega)] at hr
  simpa [description,Source284PayloadSentinelPipeline.description,shiftConfig,toSource,nextState,
    active,pairTape,Source284PayloadLoop.scratch,Nat.add_assoc] using hr

/-- Starting from the encoded input and certificate, the single finite table
constructs its own empty token side and autonomously reaches equality. -/
theorem source_pipeline (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost w.length) =
    ⟨2*pairTape (List.replicate w.length true) certificate,
      zeros w (flipped [false] (((((suffix/4)/4)/2)/2)/4^w.length)),active 281⟩ := by
  have hc := setup_closed states continuation hn hv
  have hp := Source284PayloadSentinelPipeline.source_pipeline (28+(97+states))
    (setup continuation) w certificate suffix (by omega) hc
  unfold totalCost
  rw [Source284Relative.run_add_clock,Source284Relative.run_add_clock]
  change Source284Relative.run (description states continuation)
    (Source284Relative.run (description states continuation)
      (Source284Relative.run (Source284PayloadSentinelPipeline.description (28+(97+states))
        (setup continuation)) _ _) _) _ = _
  have hs := source_setup states continuation (w++[false]) certificate ((suffix/4)/4) hn hv
  simp only [List.length_append,List.length_cons,List.length_nil] at hs
  rw [hp,hs,source_loop states continuation w certificate ((((suffix/4)/4)/2)/2) hn hv]

theorem totalCost_le (n : Nat) : totalCost n ≤ 4*n*n*n+42*n*n+110*n+75 := by
  have h := Source284RetryLoopComplete.totalCost_le 0 n (by omega)
  unfold totalCost
  rw [Source284PayloadSentinelPipeline.totalCost_formula]
  have hr : (2*n*n+26*n+36)+2*(4*(n+1)+7)+(4*n*n*n+40*n*n+76*n+17) =
      4*n*n*n+42*n*n+110*n+75 := by ring
  omega

/-- A supplied continuation executes from either final entry in the same
encoded table; the complete preprocessing prefix costs 280 states. -/
theorem source_after (states : Nat) (continuation : Nat → Bool → Row) (mode : Nat)
    (left right fuel : Nat) (hn : 2 ≤ states) (hm : mode < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) ⟨left,right,active (280+mode)⟩ fuel =
    toSource (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
      (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6 (shiftConfig 14 (shiftConfig 14
        (shiftConfig 97 (run continuation ⟨left,right,some mode⟩ fuel))))))))))))) := by
  let c : Config := ⟨left,right,some mode⟩
  have hc := setup_closed states continuation hn hv
  have hs := Source284PayloadSentinel.closed (28+(97+states)) (setup continuation) (by omega) hc
  have hvalid : Valid (142+(13+(28+(97+states))))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6
          (shiftConfig 14 (shiftConfig 14 (shiftConfig 97 c)))))))))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := Source284ScratchNormalizePipeline.source_continuation_run (13+(28+(97+states)))
    (Source284PayloadSentinel.table (setup continuation))
    (shiftConfig 7 (shiftConfig 6 (shiftConfig 14 (shiftConfig 14 (shiftConfig 97 c)))))
    fuel (by omega) hs hvalid
  rw [Source284PayloadSentinel.relocated_run,Source284ScratchFlipReturn.relocated_run] at hr
  change Source284Relative.run _ _ _ = toSource (shiftConfig 8 (shiftConfig 8 (shiftConfig 16
    (shiftConfig 32 (shiftConfig 69 (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6
      (run (Source284ScratchSentinel.special (Source284ScratchShiftCycle.table (Source284RetryLoop.table continuation)))
        (shiftConfig 14 (shiftConfig 14 (shiftConfig 97 c))) fuel)))))))))) at hr
  rw [Source284ScratchSentinel.continuation_run,Source284ScratchShiftCycle.relocated_run,
    Source284RetryLoop.relocated_run] at hr
  simpa [description,Source284PayloadSentinelPipeline.description,c,shiftConfig,toSource,nextState,
    active,← Nat.add_assoc] using hr

/-- Exhaustive parsing gives the same finite progress for every numeric
input, including empty inputs and arbitrary ignored high suffixes. -/
theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 2 ≤ states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description states continuation)
        (Source284Relative.initial input certificate) (totalCost (Source284Parser.length input)) =
    ⟨2*pairTape (List.replicate w.length true) certificate,
      zeros w (flipped [false] (((((suffix/4)/4)/2)/2)/4^w.length)),active 281⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [hlen,← hw]
  exact source_pipeline states continuation w certificate suffix hn hv

/-- The same all-input run has an explicit cubic bit-step bound. -/
theorem source_bounded_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 2 ≤ states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix t : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      t ≤ 4*(Source284Parser.length input)^3+42*(Source284Parser.length input)^2+
        110*(Source284Parser.length input)+75 ∧
      Source284Relative.run (description states continuation) (Source284Relative.initial input certificate) t =
    ⟨2*pairTape (List.replicate w.length true) certificate,
      zeros w (flipped [false] (((((suffix/4)/4)/2)/2)/4^w.length)),active 281⟩ := by
  obtain ⟨w,suffix,hw,hlen,hr⟩ := source_total_progress states continuation input certificate hn hv
  refine ⟨w,suffix,totalCost (Source284Parser.length input),hw,hlen,?_,hr⟩
  have h := totalCost_le (Source284Parser.length input)
  nlinarith

namespace Fixtures
example (states : Nat) (continuation : Nat → Bool → Row) (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 0 7) 75 =
      ⟨60,2,active 281⟩ := by
  simpa [encodeFrame,totalCost,Source284PayloadSentinelPipeline.totalCost_formula,
    Source284RetryLoopComplete.totalCost,Source284RetryLoopComplete.retriesCost,
    Source284OneRetry.cost,pairTape,Source284PayloadLoop.scratch,zeros,flipped,bit] using
    source_pipeline states continuation [] 7 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 3 7) 203 =
      ⟨242,9,active 281⟩ := by
  simpa [encodeFrame,totalCost,Source284PayloadSentinelPipeline.totalCost_formula,
    Source284RetryLoopComplete.totalCost,Source284RetryLoopComplete.retriesCost,
    Source284OneRetry.cost,pairTape,Source284PayloadLoop.scratch,zeros,flipped,bit] using
    source_pipeline states continuation [true] 7 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 295 7) 395 =
      ⟨970,33,active 281⟩ := by
  simpa [encodeFrame,totalCost,Source284PayloadSentinelPipeline.totalCost_formula,
    Source284RetryLoopComplete.totalCost,Source284RetryLoopComplete.retriesCost,
    Source284OneRetry.cost,pairTape,Source284PayloadLoop.scratch,zeros,flipped,bit] using
    source_pipeline states continuation [true,false] 7 9 hn hv
end Fixtures

end Shared.Beeping.NPcoNP.Source284RetryInitPipeline
