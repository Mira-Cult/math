import Shared.Beeping.NPcoNP.Source284LengthGrowContinue
import Shared.Beeping.NPcoNP.Source284LengthGrowSource

/-! Raw input, autonomous input-length token generation, and a paid finite
continuation in one encoded source table. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284LengthGrowRawContinue

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284LengthGrowLoop (totalTime quarters)
open Shared.Beeping.NPcoNP.Source284LengthGrowSource (setupCost totalCost)

def setup (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchUnaryRunway.setup (Source284LengthGrowContinue.table continuation)

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284PayloadSentinelPipeline.description (147+states) (setup continuation)

theorem setup_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (147+states) (setup continuation) := by
  have hc := Source284LengthGrowContinue.closed states continuation hn hv
  have hs := Source284ScratchUnaryRunway.setup_closed (119+states)
    (Source284LengthGrowContinue.table continuation) (by omega) hc
  have he : 28+(119+states) = 147+states := by omega
  rw [he] at hs
  simpa [setup] using hs

theorem setup_then (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail fuel : Nat) :
    run (setup continuation) ⟨certificate,2*flipped (w++[false]) tail,some 0⟩
      (setupCost w+(totalTime [] w+fuel)) =
    shiftConfig 147 (run continuation ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) (quarters w.length ((tail/2)/2)),some 0⟩ fuel) := by
  unfold setupCost setup
  rw [run_add,Source284ScratchUnaryRunway.setup_frame]
  change run (Source284ScratchSentinel.special
    (Source284ScratchShiftCycle.table (Source284LengthGrowContinue.table continuation)))
    (shiftConfig 14 (shiftConfig 14 ⟨pairTape [] certificate,
      2*flipped (w++[false]) ((tail/2)/2),some 0⟩)) _ = _
  rw [Source284ScratchSentinel.continuation_run,Source284ScratchShiftCycle.relocated_run,
    Source284LengthGrowContinue.produce_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]

/-- The complete finite table pays parsing, sentinel setup and every growth
round, then follows its supplied continuation for every further clock. -/
theorem source_produce_then (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) (totalCost w+fuel) =
    toSource (shiftConfig 302 (run continuation ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) (quarters w.length ((((suffix/4)/4)/2)/2)),some 0⟩ fuel)) := by
  let c : Config := ⟨certificate,2*flipped (w++[false]) ((suffix/4)/4),some 0⟩
  have hc : Valid (147+states) c := by intro q hq; simp [c] at hq; omega
  have hs := setup_closed states continuation hn hv
  have hr := run_toSource (147+states) (setup continuation) 1 c hs hc
    (setupCost w+(totalTime [] w+fuel))
  dsimp only [c] at hr
  rw [setup_then] at hr
  change Source284Relative.run (encode (147+states) (setup continuation) 1)
    (Source284Relative.initial (2*flipped (w++[false]) ((suffix/4)/4)) certificate) _ = _ at hr
  have hp := Source284SourceRelocation.source_run_after_pipeline (147+states) (setup continuation)
    w certificate suffix (setupCost w+(totalTime [] w+fuel)) (by omega) hs
  have ht : totalCost w+fuel = Source284PayloadSentinelPipeline.totalCost w.length +
      (setupCost w+(totalTime [] w+fuel)) := by simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284PayloadSentinelPipeline.description (147+states) (setup continuation))
    (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) _ = _
  rw [hp,hr,Source284SourceRelocation.lift_toSource,Source284SourceRelocation.shiftConfig_add]

/-- Full coverage of natural-number inputs, including arbitrary ignored suffixes. -/
theorem source_all_inputs_then (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      Source284Parser.encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description states continuation)
        (Source284Relative.initial input certificate) (totalCost w+fuel) =
      toSource (shiftConfig 302 (run continuation ⟨pairTape (List.replicate w.length false) certificate,
        2*flipped (w++[false]) (quarters w.length ((((suffix/4)/4)/2)/2)),some 0⟩ fuel)) := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [← hw]
  exact source_produce_then states continuation w certificate suffix fuel hn hv

end Shared.Beeping.NPcoNP.Source284LengthGrowRawContinue
