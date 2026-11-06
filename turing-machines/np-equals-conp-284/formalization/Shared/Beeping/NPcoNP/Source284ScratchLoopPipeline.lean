import Shared.Beeping.NPcoNP.Source284ScratchShiftLoop

/-! A single fixed encoded source table first creates the scratch stream and
then executes any finite number of iterations of the same looping table. The
loop has no exit condition; no bounded loader or beeper endpoint is claimed. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchLoopPipeline

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

def description : Nat :=
  Source284ScratchFlipPipeline.description 14 Source284ScratchShiftLoop.table

def elapsed (count n : Nat) : Nat :=
  Source284ScratchFlipPipeline.totalCost n + count*(4*n+7)

/-- The same encoded table performs every finite number of loop cycles from
the scratch boundary. The index is used only in the theorem's clock. -/
theorem source_iterations (count : Nat) (w : List Bool) (certificate tail : Nat) :
    Source284Relative.run description
      ⟨certificate,2*flipped w tail,active 142⟩ (count*(4*w.length+7)) =
      ⟨2^count*certificate,2*flipped w (tail/2^count),active 142⟩ := by
  let c : Config := ⟨certificate,2*flipped w tail,some 0⟩
  have hvalid : Valid (142+14)
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 c))))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := Source284ScratchNormalizePipeline.source_continuation_run 14
    Source284ScratchShiftLoop.table c (count*(4*w.length+7)) (by decide)
    Source284ScratchShiftLoop.closed hvalid
  dsimp only [c] at hr
  rw [Source284ScratchShiftLoop.iterations] at hr
  simpa [description,shiftConfig,toSource,nextState,active,Nat.add_assoc] using hr

/-- Starting at the original framed input, the fixed source program reaches
the stated tape configuration after its initial pack and any chosen number
of actual loop cycles. -/
theorem source_pipeline (count : Nat) (w : List Bool) (certificate suffix : Nat) :
    Source284Relative.run description (Source284Relative.initial (encodeFrame w suffix) certificate)
      (elapsed count w.length) =
      ⟨2^count*certificate,2*flipped w ((suffix/4)/2^count),active 142⟩ := by
  unfold elapsed description
  rw [Source284Relative.run_add_clock,
    Source284ScratchFlipPipeline.source_pipeline 14 Source284ScratchShiftLoop.table
      w certificate suffix (by decide) Source284ScratchShiftLoop.closed]
  change Source284Relative.run description _ _ = _
  rw [source_iterations]

/-- After the finite pack phase, every subsequent source step remains in a
continuing state. This is not a beeping or eventual-silence statement. -/
theorem source_continues_after_pack (w : List Bool) (certificate suffix fuel : Nat) :
    (Source284Relative.run description (Source284Relative.initial (encodeFrame w suffix) certificate)
      (Source284ScratchFlipPipeline.totalCost w.length+fuel)).state ≠ 0 := by
  let c : Config := ⟨certificate,2*flipped w (suffix/4),some 0⟩
  have hc : Valid 14 c := by
    intro q hq
    simp [c] at hq
    subst q
    decide
  have ha : c.state.isSome = true := rfl
  have hactive := Source284ScratchShiftLoop.run_continues c hc ha fuel
  have hvalid : Valid (142+14)
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 c))))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := Source284ScratchNormalizePipeline.source_continuation_run 14
    Source284ScratchShiftLoop.table c fuel (by decide) Source284ScratchShiftLoop.closed hvalid
  change Source284Relative.run description
    ⟨certificate,2*flipped w (suffix/4),active 142⟩ fuel = _ at hr
  have hp : Source284Relative.run description
      (Source284Relative.initial (encodeFrame w suffix) certificate)
      (Source284ScratchFlipPipeline.totalCost w.length) =
      ⟨certificate,2*flipped w (suffix/4),active 142⟩ := by
    exact Source284ScratchFlipPipeline.source_pipeline 14 Source284ScratchShiftLoop.table
      w certificate suffix (by decide) Source284ScratchShiftLoop.closed
  rw [Source284Relative.run_add_clock,hp,hr]
  cases he : (run Source284ScratchShiftLoop.table c fuel).state with
  | none => simp [he] at hactive
  | some q => simp [shiftConfig,toSource,nextState,active,he]

/-- The table has the same finite-prefix behavior for every numeric input;
its loop count remains a theorem index, not machine input. -/
theorem source_total_progress (count input certificate : Nat) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run description (Source284Relative.initial input certificate)
        (elapsed count (Source284Parser.length input)) =
        ⟨2^count*certificate,2*flipped w ((suffix/4)/2^count),active 142⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [hlen,← hw]
  exact source_pipeline count w certificate suffix

theorem elapsed_formula (count n : Nat) :
    elapsed count n = 2*n*n+22*n+24+count*(4*n+7) := by
  rw [elapsed,Source284ScratchFlipPipeline.totalCost_formula]

namespace Fixtures
example : Source284Relative.run description (Source284Relative.initial 295 7) 106 =
    ⟨28,22,active 142⟩ := by
  simpa [encodeFrame,elapsed_formula,flipped,bit] using source_pipeline 2 [true,false] 7 9

example : Source284Relative.run description (Source284Relative.initial 0 7) 38 =
    ⟨28,0,active 142⟩ := by
  simpa [encodeFrame,elapsed_formula,flipped] using source_pipeline 2 [] 7 0
end Fixtures

end Shared.Beeping.NPcoNP.Source284ScratchLoopPipeline
