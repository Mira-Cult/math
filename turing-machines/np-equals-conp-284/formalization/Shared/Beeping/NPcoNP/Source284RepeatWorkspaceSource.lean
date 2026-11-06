import Shared.Beeping.NPcoNP.Source284RepeatWorkspace

/-! Source-level raw-input execution for a compile-time fixed number of
clean workspace passes. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284RepeatWorkspaceSource

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284RepeatWorkspace

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284PayloadSentinelPipeline.description (226*k+states) (repeatTable k continuation)

def elapsed (k : Nat) (w : List Bool) : Nat :=
  Source284PayloadSentinelPipeline.totalCost w.length+k*roundCost w

/-- Raw-input initialization and all k compiled passes are actual source
execution. The arbitrary supplied continuation then runs for `fuel` steps. -/
theorem source_then (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) (elapsed k w+fuel) =
    toSource (shiftConfig (155+226*k) (run continuation
      ⟨2^(k*(3*(w.length+1)))*certificate,
        2*flipped (w++[false]) (iterateTail k w.length ((suffix/4)/4)),some 0⟩ fuel)) := by
  let c : Config := ⟨certificate,2*flipped (w++[false]) ((suffix/4)/4),some 0⟩
  have hv0 : Valid (226*k+states) c := by intro q hq; simp [c] at hq; omega
  have hc := repeat_closed k states continuation hn hv
  have hr := run_toSource (226*k+states) (repeatTable k continuation) 1 c hc hv0 (k*roundCost w+fuel)
  dsimp only [c] at hr
  rw [repeat_then] at hr
  change Source284Relative.run (encode (226*k+states) (repeatTable k continuation) 1)
    (Source284Relative.initial (2*flipped (w++[false]) ((suffix/4)/4)) certificate) _ = _ at hr
  have hp := Source284SourceRelocation.source_run_after_pipeline (226*k+states) (repeatTable k continuation)
    w certificate suffix (k*roundCost w+fuel) (by omega) hc
  have ht : elapsed k w+fuel = Source284PayloadSentinelPipeline.totalCost w.length +
      (k*roundCost w+fuel) := by simp [elapsed]; omega
  rw [ht]
  change Source284Relative.run (Source284PayloadSentinelPipeline.description (226*k+states) (repeatTable k continuation))
    (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) _ = _
  rw [hp,hr,Source284SourceRelocation.lift_toSource,Source284SourceRelocation.shiftConfig_add]

theorem elapsed_formula (k : Nat) (w : List Bool) :
    3*elapsed k w = 6*w.length*w.length+78*w.length+108 +
      k*(4*w.length*w.length*w.length+111*w.length*w.length+404*w.length+309) := by
  rw [elapsed,Source284PayloadSentinelPipeline.totalCost_formula]
  calc
    3*(2*w.length*w.length+26*w.length+36+k*roundCost w) =
        3*(2*w.length*w.length+26*w.length+36)+k*(3*roundCost w) := by ring
    _ = _ := by rw [roundCost_formula]; ring

/-- The source-table size includes all initialization, all compiled passes,
and the supplied continuation. -/
def sourceTable (k : Nat) (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchFlipPipeline.table (Source284PayloadSentinel.table (repeatTable k continuation))

theorem description_eq (k states : Nat) (continuation : Nat → Bool → Row) :
    description k states continuation = encode (155+226*k+states) (sourceTable k continuation) 1 := by
  unfold description Source284PayloadSentinelPipeline.description
    Source284ScratchFlipPipeline.description sourceTable
  congr 1
  omega

theorem record_count (k states : Nat) (continuation : Nat → Bool → Row) :
    (records (155+226*k+states) (sourceTable k continuation)).length =
      2*(155+226*k+states) := by
  simp [records]

/-- Coverage of all numeric inputs also retains the complete continuation run. -/
theorem source_all_inputs_then (k states : Nat) (continuation : Nat → Bool → Row)
    (input certificate fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      Source284Parser.encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial input certificate) (elapsed k w+fuel) =
      toSource (shiftConfig (155+226*k) (run continuation
        ⟨2^(k*(3*(w.length+1)))*certificate,
          2*flipped (w++[false]) (iterateTail k w.length ((suffix/4)/4)),some 0⟩ fuel)) := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [← hw]
  exact source_then k states continuation w certificate suffix fuel hn hv

/-- Every numeric input reaches the continuation with the displayed number
of low zeros; the number of passes is a fixed program parameter. -/
theorem source_all_inputs (k states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix left right : Nat),
      Source284Parser.encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial input certificate) (elapsed k w) =
          ⟨left,right,active (155+226*k)⟩ ∧
      2^(k*(3*(w.length+1))) ∣ left := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,2^(k*(3*(w.length+1)))*certificate,
    2*flipped (w++[false]) (iterateTail k w.length ((suffix/4)/4)),hw,hlen.symm,?_,?_⟩
  · rw [← hw]
    have h := source_then k states continuation w certificate suffix 0 hn hv
    simpa [run,shiftConfig,toSource,nextState,active] using h
  · exact dvd_mul_right _ _

namespace Fixtures
example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description 1 states continuation) (Source284Relative.initial 0 7) 139 =
      ⟨56,4,active 381⟩ := by
  have h := source_then 1 states continuation [] 7 0 0 hn hv
  have ht : elapsed 1 [] = 139 := by
    have hc := elapsed_formula 1 []
    simp at hc
    omega
  rw [ht] at h
  simpa [run,shiftConfig,toSource,nextState,active,Source284Parser.encodeFrame,
    flipped,iterateTail,nextTail,Source284LengthGrowLoop.quarters,
    Source284TokenCounterLoop.halves,bit] using h

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description 2 states continuation) (Source284Relative.initial 0 7) 242 =
      ⟨448,4,active 607⟩ := by
  have h := source_then 2 states continuation [] 7 0 0 hn hv
  have ht : elapsed 2 [] = 242 := by
    have hc := elapsed_formula 2 []
    simp at hc
    omega
  rw [ht] at h
  simpa [run,shiftConfig,toSource,nextState,active,Source284Parser.encodeFrame,
    flipped,iterateTail,nextTail,Source284LengthGrowLoop.quarters,
    Source284TokenCounterLoop.halves,bit] using h
end Fixtures

end Shared.Beeping.NPcoNP.Source284RepeatWorkspaceSource
