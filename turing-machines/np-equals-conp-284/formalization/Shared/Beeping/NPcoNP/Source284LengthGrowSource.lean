import Shared.Beeping.NPcoNP.Source284LengthGrowTime
import Shared.Beeping.NPcoNP.Source284ScratchUnaryRunway
import Shared.Beeping.NPcoNP.Source284SourceRelocation

/-! Raw numeric inputs initialize an empty unary sentinel, then one finite
source program autonomously grows exactly one token per parsed payload bit. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284LengthGrowSource

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284LengthGrowLoop

def setup : Nat → Bool → Row := Source284ScratchUnaryRunway.setup table

def description : Nat := Source284PayloadSentinelPipeline.description 147 setup

def setupCost (w : List Bool) : Nat := 2*(4*(w++[false]).length+7)

def totalCost (w : List Bool) : Nat :=
  Source284PayloadSentinelPipeline.totalCost w.length + (setupCost w + totalTime [] w)

theorem setup_closed : Closed 147 setup := by
  have h := Source284ScratchUnaryRunway.setup_closed 119 table (by decide) closed
  simpa [setup] using h

/-- The initializer creates the empty token sentinel, then all autonomous
growth cycles run inside that same finite table. -/
theorem setup_produce (w : List Bool) (certificate tail : Nat) :
    run setup ⟨certificate,2*flipped (w++[false]) tail,some 0⟩ (setupCost w+totalTime [] w) =
    ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) (quarters w.length ((tail/2)/2)),some 146⟩ := by
  unfold setupCost setup
  rw [run_add,Source284ScratchUnaryRunway.setup_frame]
  change run (Source284ScratchSentinel.special (Source284ScratchShiftCycle.table table))
    (shiftConfig 14 (shiftConfig 14 ⟨pairTape [] certificate,
      2*flipped (w++[false]) ((tail/2)/2),some 0⟩)) _ = _
  rw [Source284ScratchSentinel.continuation_run,Source284ScratchShiftCycle.relocated_run,
    produce_from_zero]
  rfl

/-- A single numeric source table starts on the actual raw frame and reaches
the equality state after creating exactly one unmarked token per payload bit. -/
theorem source_produce (w : List Bool) (certificate suffix : Nat) :
    Source284Relative.run description
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) (totalCost w) =
    ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) (quarters w.length ((((suffix/4)/4)/2)/2)),active 301⟩ := by
  let c : Config := ⟨certificate,2*flipped (w++[false]) ((suffix/4)/4),some 0⟩
  have hc : Valid 147 c := by intro q hq; simp [c] at hq; omega
  have hr := run_toSource 147 setup 1 c setup_closed hc (setupCost w+totalTime [] w)
  dsimp only [c] at hr
  rw [setup_produce] at hr
  change Source284Relative.run (encode 147 setup 1)
    (Source284Relative.initial (2*flipped (w++[false]) ((suffix/4)/4)) certificate) _ = _ at hr
  have hp := Source284SourceRelocation.source_run_after_pipeline 147 setup w certificate suffix
    (setupCost w+totalTime [] w) (by decide) setup_closed
  change Source284Relative.run description
    (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) (totalCost w) = _ at hp
  rw [hr] at hp
  simpa [Source284SourceRelocation.lift,active,toSource,nextState] using hp

/-- Parser coverage includes zero and every high-suffix alias; the eventual
entry state is reached in a finite execution of the same source description. -/
theorem source_all_inputs (input certificate : Nat) :
    ∃ (w : List Bool) (suffix : Nat),
      Source284Parser.encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run description (Source284Relative.initial input certificate) (totalCost w) =
      ⟨pairTape (List.replicate w.length false) certificate,
        2*flipped (w++[false]) (quarters w.length ((((suffix/4)/4)/2)/2)),active 301⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [← hw]
  exact source_produce w certificate suffix

/-- Exact cubic total, including raw parsing and sentinel initialization. -/
theorem totalCost_formula (w : List Bool) :
    3*totalCost w = 4*w.length*w.length*w.length+84*w.length*w.length+326*w.length+282 := by
  have h := Source284LengthGrowTime.zero_formula w
  rw [totalCost,Source284PayloadSentinelPipeline.totalCost_formula]
  simp only [setupCost,List.length_append,List.length_singleton]
  nlinarith

namespace Fixtures
example : Source284Relative.run description (Source284Relative.initial 0 0) 94 =
    ⟨2,4,active 301⟩ := by
  have h := source_produce [] 0 0
  have ht : totalCost [] = 94 := by
    have hc := totalCost_formula []
    simp at hc
    omega
  rw [ht] at h
  simpa [Source284Parser.encodeFrame,pairTape,Source284PayloadLoop.scratch,flipped,
    quarters,bit] using h

example : Source284Relative.run description (Source284Relative.initial 1 0) 232 =
    ⟨8,20,active 301⟩ := by
  have h := source_produce [false] 0 0
  have ht : totalCost [false] = 232 := by
    have hc := totalCost_formula [false]
    simp at hc
    omega
  rw [ht] at h
  simpa [Source284Parser.encodeFrame,pairTape,Source284PayloadLoop.scratch,flipped,
    quarters,bit] using h
end Fixtures

end Shared.Beeping.NPcoNP.Source284LengthGrowSource
