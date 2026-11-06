import Shared.Beeping.NPcoNP.Source284ScratchNormalize

/-! Compose the source's finite scratch pipeline with the checked finite
normalizer. This reaches a framed input and retained certificate on the
actual source table; it does not construct the canonical verifier pair. -/
set_option maxHeartbeats 2000000

namespace Shared.Beeping.NPcoNP.Source284ScratchNormalizePipeline

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchFlipPipeline.table (Source284ScratchNormalize.table continuation)

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284ScratchFlipPipeline.description (68+states) (Source284ScratchNormalize.table continuation)

def totalCost (n : Nat) : Nat := Source284ScratchFlipPipeline.totalCost n + (6*n+11)

theorem totalCost_formula (n : Nat) : totalCost n = 2*n*n+28*n+35 := by
  rw [totalCost,Source284ScratchFlipPipeline.totalCost_formula]
  ring

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (210+states) (table continuation) := by
  have h : Closed (68+states) (Source284ScratchNormalize.table continuation) := by
    have he : 36+(32+states) = 68+states := by omega
    rw [← he]
    exact Source284ScratchNormalize.closed states continuation hn hv
  have h' := Source284ScratchFlipPipeline.closed (68+states)
    (Source284ScratchNormalize.table continuation) (by omega) h
  have he : 142+(68+states) = 210+states := by omega
  rw [he] at h'
  exact h'

/-- The earlier source prefix forwards an arbitrary continuation's run with
all steps and state offsets accounted for. -/
theorem prefix_relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (Source284ScratchFlipPipeline.table continuation)
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 c))))))) clock =
      shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 (run continuation c clock))))))) := by
  change run (Source284InputSentinel.table
    (Source284ModePrefixScan.table (Source284ScratchTerminator.table
      (Source284PayloadLoop.table (Source284ScratchFlip.table (Source284ScratchFlipReturn.table continuation)))))) _ _ = _
  rw [Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    Source284ScratchTerminator.relocated_run,Source284ModePrefixReturn.relocated_run,
    Source284PayloadLoop.relocated_run,Source284ScratchFlip.relocated_run,
    Source284ScratchFlipReturn.relocated_run]

/-- Transfer the arbitrary continuation run through the encoded source
prefix, retaining the complete configuration and every charged step. -/
theorem source_continuation_run (states : Nat) (continuation : Nat → Bool → Row)
    (c : Config) (clock : Nat) (hn : 0 < states) (hv : Closed states continuation)
    (hvalid : Valid (142+states)
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 c)))))))) :
    Source284Relative.run (Source284ScratchFlipPipeline.description states continuation)
      (toSource (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 c)))))))) clock =
      toSource (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 (run continuation c clock)))))))) := by
  have hr := run_toSource (142+states) (Source284ScratchFlipPipeline.table continuation) 1
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
      (shiftConfig 3 (shiftConfig 6 c))))))) (Source284ScratchFlipPipeline.closed states continuation hn hv) hvalid clock
  change Source284Relative.run (Source284ScratchFlipPipeline.description states continuation) _ _ = _ at hr
  rw [prefix_relocated_run] at hr
  exact hr

/-- Starting at the scratch boundary, the encoded table executes the finite
normalizer segment with all state offsets accounted for. -/
theorem source_normalize (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate tail : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      ⟨certificate,2*flipped w tail,active 142⟩ (6*w.length+11) =
      ⟨2*certificate,encodeFrame w (2*tail+1),active 210⟩ := by
  let c : Config := ⟨certificate,2*flipped w tail,some 0⟩
  have hclosed : Closed (68+states) (Source284ScratchNormalize.table continuation) := by
    have he : 36+(32+states) = 68+states := by omega
    rw [← he]
    exact Source284ScratchNormalize.closed states continuation hn hv
  have hvalid : Valid (142+(68+states))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 c))))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := source_continuation_run (68+states) (Source284ScratchNormalize.table continuation)
    c (6*w.length+11) (by omega) hclosed hvalid
  dsimp only [c] at hr
  rw [Source284ScratchNormalize.normalize] at hr
  simpa [description,shiftConfig,toSource,nextState,active,Nat.add_assoc] using hr

/-- The actual encoded source program completes both parts on every framed
input, preserving the certificate one cell to the left of the new head. -/
theorem source_pipeline (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost w.length) =
      ⟨2*certificate,encodeFrame w (2*(suffix/4)+1),active 210⟩ := by
  have h : Closed (68+states) (Source284ScratchNormalize.table continuation) := by
    have he : 36+(32+states) = 68+states := by omega
    rw [← he]
    exact Source284ScratchNormalize.closed states continuation hn hv
  unfold totalCost description
  rw [Source284Relative.run_add_clock,
    Source284ScratchFlipPipeline.source_pipeline (68+states)
      (Source284ScratchNormalize.table continuation) w certificate suffix (by omega) h]
  change Source284Relative.run (description states continuation) _ _ = _
  rw [source_normalize states continuation w certificate (suffix/4) hn hv]

/-- Termination applies to every numeric input, including zero. -/
theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description states continuation)
        (Source284Relative.initial input certificate) (totalCost (Source284Parser.length input)) =
        ⟨2*certificate,encodeFrame w (2*(suffix/4)+1),active 210⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [hlen,← hw]
  exact source_pipeline states continuation w certificate suffix hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial 0 0) 35 = ⟨0,2,active 210⟩ := by
  simpa [encodeFrame,totalCost_formula] using source_pipeline states continuation [] 0 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial 295 7) 99 = ⟨14,167,active 210⟩ := by
  simpa [encodeFrame,totalCost_formula] using
    source_pipeline states continuation [true,false] 7 9 hn hv

end Shared.Beeping.NPcoNP.Source284ScratchNormalizePipeline
