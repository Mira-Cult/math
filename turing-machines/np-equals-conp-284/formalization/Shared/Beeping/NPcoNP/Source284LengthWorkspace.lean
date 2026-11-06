import Shared.Beeping.NPcoNP.Source284FlippedCounterSeed
import Shared.Beeping.NPcoNP.Source284TokenCounterContinue
import Shared.Beeping.NPcoNP.Source284RawCounterShift
import Shared.Beeping.NPcoNP.Source284LengthGrowRawContinue

/-! Compose the raw-input unary length producer with a paid counter seed,
token loop and counted shift. No unary tokens are supplied in the input. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284LengthWorkspace

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (consumeTime halves)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284FlippedCounterSeed.table
    (Source284TokenCounterLoop.table (Source284RawCounterShift.adapter continuation))

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (71+states) (table continuation) := by
  have ha := Source284RawCounterShift.adapter_closed states continuation hn hv
  have hl := Source284TokenCounterLoop.closed (23+states)
    (Source284RawCounterShift.adapter continuation) (by omega) ha
  have hs := Source284FlippedCounterSeed.closed (32+(23+states))
    (Source284TokenCounterLoop.table (Source284RawCounterShift.adapter continuation)) (by omega) hl
  have he : 16+(32+(23+states)) = 71+states := by omega
  rw [he] at hs
  exact hs

def workCost (m width : Nat) : Nat :=
  (4*width+14) + (consumeTime m 0 0 width + (2+(m+1)*(4*width+7)))

/-- From a token tape and flipped input frame, the finite source table seeds
and counts the tokens, inserts `m+1` zero cells, and runs its continuation. -/
theorem workspace_then (continuation : Nat → Bool → Row) (m : Nat) (w : List Bool)
    (certificate suffix fuel : Nat) :
    run (table continuation) ⟨pairTape (List.replicate m false) certificate,
      2*flipped w suffix,some 0⟩ (workCost m w.length+fuel) =
    shiftConfig 71 (run continuation
      ⟨2^(m+1)*pairTape (List.replicate m true) certificate,
        2*flipped w (halves m (suffix/2)),some 0⟩ fuel) := by
  have ht : workCost m w.length+fuel = (4*w.length+14) +
      (consumeTime m 0 0 w.length + (2+((m+1)*(4*w.length+7)+fuel))) := by
    simp [workCost]; omega
  rw [ht]
  unfold table
  rw [Source284FlippedCounterSeed.seed_then,run_add]
  have hc := Source284TokenCounterLoop.consume (Source284RawCounterShift.adapter continuation)
    m 0 w 0 certificate (suffix/2)
  simp only [List.replicate_zero,List.nil_append,Nat.zero_add] at hc
  rw [hc]
  change shiftConfig 16 (run (Source284TokenCounterLoop.table (Source284RawCounterShift.adapter continuation))
    (shiftConfig 32 ⟨pairTape (List.replicate m true) certificate,
      2*flipped w (counter m (halves m (suffix/2))),some 1⟩) _) = _
  rw [Source284TokenCounterContinue.relocated_run,run_add,Source284RawCounterShift.enter]
  change shiftConfig 16 (shiftConfig 32 (run (Source284RawCounterShift.adapter continuation)
    (shiftConfig 2 ⟨pairTape (List.replicate m true) certificate,
      2*flipped w (counter m (halves m (suffix/2))),some 0⟩) _)) = _
  rw [Source284RawCounterShift.relocated_run,Source284CountedShift.countdown_after]
  repeat rw [Source284SourceRelocation.shiftConfig_add]

/-- Cost of generating a linear runway from an input frame of payload length n. -/
theorem workCost_formula (n : Nat) : workCost n (n+1) = 11*n*n+48*n+39 := by
  rw [workCost,Source284TokenCounterLoop.consumeTime_formula]
  ring

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284LengthGrowRawContinue.description (71+states) (table continuation)

def totalCost (w : List Bool) : Nat :=
  Source284LengthGrowSource.totalCost w + workCost w.length (w++[false]).length

def retained (n suffix : Nat) : Nat :=
  halves n (Source284LengthGrowLoop.quarters n ((((suffix/4)/4)/2)/2)/2)

/-- From the raw numeric input and arbitrary certificate, a single encoded
source table makes a linear block of zero cells and executes the supplied
continuation, with all initialization and run time charged. -/
theorem source_workspace_then (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) (totalCost w+fuel) =
    toSource (shiftConfig 373 (run continuation
      ⟨2^(w.length+1)*pairTape (List.replicate w.length true) certificate,
        2*flipped (w++[false]) (retained w.length suffix),some 0⟩ fuel)) := by
  have hc := closed states continuation hn hv
  have hp := Source284LengthGrowRawContinue.source_produce_then (71+states) (table continuation)
    w certificate suffix (workCost w.length (w++[false]).length+fuel) (by omega) hc
  have ht : totalCost w+fuel = Source284LengthGrowSource.totalCost w +
      (workCost w.length (w++[false]).length+fuel) := by simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284LengthGrowRawContinue.description (71+states) (table continuation))
    (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) _ = _
  rw [hp,workspace_then,Source284SourceRelocation.shiftConfig_add]
  rfl

theorem totalCost_formula (w : List Bool) :
    3*totalCost w = 4*w.length*w.length*w.length+117*w.length*w.length+470*w.length+399 := by
  have h := Source284LengthGrowSource.totalCost_formula w
  rw [totalCost]
  simp only [List.length_append,List.length_singleton,workCost_formula]
  nlinarith

/-- Parser coverage and subsequent continuation execution for every numeric input. -/
theorem source_all_inputs_then (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      Source284Parser.encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description states continuation)
        (Source284Relative.initial input certificate) (totalCost w+fuel) =
      toSource (shiftConfig 373 (run continuation
        ⟨2^(w.length+1)*pairTape (List.replicate w.length true) certificate,
          2*flipped (w++[false]) (retained w.length suffix),some 0⟩ fuel)) := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [← hw]
  exact source_workspace_then states continuation w certificate suffix fuel hn hv

/-- Every natural input reaches the continuation with at least `n+1` low
zero cells on its opposite tape half; no bound or token tape is preloaded. -/
theorem source_all_inputs (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix left right : Nat),
      Source284Parser.encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description states continuation)
        (Source284Relative.initial input certificate) (totalCost w) = ⟨left,right,active 373⟩ ∧
      2^(w.length+1) ∣ left := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,2^(w.length+1)*pairTape (List.replicate w.length true) certificate,
    2*flipped (w++[false]) (retained w.length suffix),hw,hlen.symm,?_,?_⟩
  · rw [← hw]
    have h := source_workspace_then states continuation w certificate suffix 0 hn hv
    simpa [run,shiftConfig,toSource,nextState,active] using h
  · exact dvd_mul_right _ _

namespace Fixtures
example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 0 0) 133 =
      ⟨4,4,active 373⟩ := by
  have h := source_workspace_then states continuation [] 0 0 0 hn hv
  have ht : totalCost [] = 133 := by
    have hc := totalCost_formula []
    simp at hc
    omega
  rw [ht] at h
  simpa [run,shiftConfig,toSource,nextState,active,Source284Parser.encodeFrame,pairTape,
    Source284PayloadLoop.scratch,flipped,retained,halves,Source284LengthGrowLoop.quarters,bit] using h

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 1 0) 330 =
      ⟨36,20,active 373⟩ := by
  have h := source_workspace_then states continuation [false] 0 0 0 hn hv
  have ht : totalCost [false] = 330 := by
    have hc := totalCost_formula [false]
    simp at hc
    omega
  rw [ht] at h
  simpa [run,shiftConfig,toSource,nextState,active,Source284Parser.encodeFrame,pairTape,
    Source284PayloadLoop.scratch,flipped,retained,halves,Source284LengthGrowLoop.quarters,bit] using h
end Fixtures

end Shared.Beeping.NPcoNP.Source284LengthWorkspace
