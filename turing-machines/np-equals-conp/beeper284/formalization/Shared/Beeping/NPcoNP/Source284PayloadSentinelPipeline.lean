import Shared.Beeping.NPcoNP.Source284PayloadSentinel
import Shared.Beeping.NPcoNP.Source284ScratchNormalizePipeline

/-! Compose the finite sentinel pass with the framed-input source pipeline.
The added false pair is a sentinel and must not be counted as input payload. -/
namespace Shared.Beeping.NPcoNP.Source284PayloadSentinelPipeline

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284ScratchFlipPipeline.description (13+states) (Source284PayloadSentinel.table continuation)

def totalCost (n : Nat) : Nat := Source284ScratchFlipPipeline.totalCost n+(4*n+12)

theorem totalCost_formula (n : Nat) : totalCost n = 2*n*n+26*n+36 := by
  rw [totalCost,Source284ScratchFlipPipeline.totalCost_formula]
  ring

theorem source_install (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate tail : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      ⟨certificate,2*flipped w tail,active 142⟩ (4*w.length+12) =
      ⟨certificate,2*flipped (w++[false]) (tail/4),active 155⟩ := by
  let c : Config := ⟨certificate,2*flipped w tail,some 0⟩
  have hc := Source284PayloadSentinel.closed states continuation hn hv
  have hvalid : Valid (142+(13+states))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 c))))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := Source284ScratchNormalizePipeline.source_continuation_run (13+states)
    (Source284PayloadSentinel.table continuation) c (4*w.length+12) (by omega) hc hvalid
  dsimp only [c] at hr
  rw [Source284PayloadSentinel.install] at hr
  simpa [description,shiftConfig,toSource,nextState,active,Nat.add_assoc] using hr

theorem source_pipeline (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost w.length) =
      ⟨certificate,2*flipped (w++[false]) ((suffix/4)/4),active 155⟩ := by
  have hc := Source284PayloadSentinel.closed states continuation hn hv
  unfold totalCost
  rw [Source284Relative.run_add_clock]
  change Source284Relative.run (description states continuation)
    (Source284Relative.run (Source284ScratchFlipPipeline.description (13+states)
      (Source284PayloadSentinel.table continuation)) _ _) _ = _
  rw [Source284ScratchFlipPipeline.source_pipeline (13+states)
    (Source284PayloadSentinel.table continuation) w certificate suffix (by omega) hc]
  exact source_install states continuation w certificate (suffix/4) hn hv

theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description states continuation)
        (Source284Relative.initial input certificate) (totalCost (Source284Parser.length input)) =
      ⟨certificate,2*flipped (w++[false]) ((suffix/4)/4),active 155⟩ ∧
      Source284ScratchFlipDecode.decode (flipped (w++[false]) ((suffix/4)/4)) = some (w++[false]) ∧
      Source284ScratchFlipDecode.inspections (flipped (w++[false]) ((suffix/4)/4)) = w.length+2 := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_,Source284ScratchFlipDecode.decode_flipped _ _,?_⟩
  · rw [hlen,← hw]
    exact source_pipeline states continuation w certificate suffix hn hv
  · simpa using Source284ScratchFlipDecode.inspections_flipped (w++[false]) ((suffix/4)/4)

/-- After the charged installation, execution is that of the supplied
finite continuation on the restored certificate and sentinel-framed tape. -/
theorem source_after_pipeline (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix clock : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.accepts (description states continuation) (encodeFrame w suffix) certificate
      (totalCost w.length+clock) =
    Source284Relative.accepts (encode states continuation 1)
      (2*flipped (w++[false]) ((suffix/4)/4)) certificate clock := by
  let c : Config := ⟨certificate,2*flipped (w++[false]) ((suffix/4)/4),some 0⟩
  have hc := Source284PayloadSentinel.closed states continuation hn hv
  have h0 : Valid states c := by
    intro q hq
    simp [c] at hq
    subst q
    exact hn
  have h1 : Valid (142+(13+states))
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6 c))))))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr1 := run_toSource (142+(13+states))
    (Source284ScratchFlipPipeline.table (Source284PayloadSentinel.table continuation)) 1
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
      (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6 c)))))))))
    (Source284ScratchFlipPipeline.closed (13+states) (Source284PayloadSentinel.table continuation)
      (by omega) hc) h1 clock
  have hr0 := run_toSource states continuation 1 c hv h0 clock
  change Source284Relative.run (description states continuation)
    ⟨certificate,2*flipped (w++[false]) ((suffix/4)/4),
      active (8+(8+(16+(32+(69+(3+(6+(7+6))))))))⟩ clock = _ at hr1
  have hs : 8+(8+(16+(32+(69+(3+(6+(7+6))))))) = 155 := by omega
  rw [hs] at hr1
  change Source284Relative.run (encode states continuation 1)
    (Source284Relative.initial (2*flipped (w++[false]) ((suffix/4)/4)) certificate) clock = _ at hr0
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_pipeline states continuation w certificate suffix hn hv,hr1,hr0]
  change ((toSource (run (Source284InputSentinel.table
    (Source284ModePrefixScan.table (Source284ScratchTerminator.table
      (Source284PayloadLoop.table (Source284ScratchFlip.table (Source284ScratchFlipReturn.table
        (Source284PayloadSentinel.table continuation)))))))
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
      (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6 c))))))))) clock)).state == 0) =
        ((toSource (run continuation c clock)).state == 0)
  rw [Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    Source284ScratchTerminator.relocated_run,Source284ModePrefixReturn.relocated_run,
    Source284PayloadLoop.relocated_run,Source284ScratchFlip.relocated_run,
    Source284ScratchFlipReturn.relocated_run,Source284PayloadSentinel.relocated_run,
    Source284ScratchFlipReturn.relocated_run]
  cases h : (run continuation c clock).state <;>
    simp [toSource,shiftConfig,nextState,h,active]

namespace Fixtures
example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial 0 7) 36 = ⟨7,4,active 155⟩ := by
  simpa [encodeFrame,totalCost,Source284ScratchFlipPipeline.totalCost,
    Source284ScratchPack.totalCost,Source284PayloadLoop.cost,flipped,bit] using
    source_pipeline states continuation [] 7 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial 295 7) 96 = ⟨7,86,active 155⟩ := by
  simpa [encodeFrame,totalCost,Source284ScratchFlipPipeline.totalCost,
    Source284ScratchPack.totalCost,Source284PayloadLoop.cost,flipped,bit] using
    source_pipeline states continuation [true,false] 7 9 hn hv
end Fixtures

end Shared.Beeping.NPcoNP.Source284PayloadSentinelPipeline
