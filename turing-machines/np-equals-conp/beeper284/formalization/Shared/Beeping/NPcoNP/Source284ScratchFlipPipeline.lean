import Shared.Beeping.NPcoNP.Source284ScratchFlipReturn
import Shared.Beeping.NPcoNP.Source284ScratchFlipDecode

/-! A finite source program packs the raw payload, flips scratch markers,
and makes a self-delimiting reverse pass. Its continuation receives the head
back at the original boundary and the entire certificate. This is not yet
canonical pair/witness packing or a physical beeper theorem. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchFlipPipeline

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284PayloadLoop (scratch)
open Shared.Beeping.NPcoNP.Source284ScratchTerminator (mark)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (push flipped)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchPack.table (Source284ScratchFlip.table (Source284ScratchFlipReturn.table continuation))

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  encode (142+states) (table continuation) 1

def totalCost (n : Nat) : Nat := Source284ScratchPack.totalCost n+(2*n+3)+(2*n+5)

theorem totalCost_formula (n : Nat) : totalCost n = 2*n*n+22*n+24 := by
  rw [totalCost,Source284ScratchPack.totalCost_formula]
  ring

theorem totalCost_positive (n : Nat) : 0 < totalCost n := by
  rw [totalCost_formula]
  omega

theorem record_count (states : Nat) (continuation : Nat → Bool → Row) :
    (records (142+states) (table continuation)).length = 2*(142+states) := by
  simp [records]

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (142+states) (table continuation) := by
  have h0 := Source284ScratchFlipReturn.closed states continuation hn hv
  have h1 := Source284ScratchFlip.closed (6+states) (Source284ScratchFlipReturn.table continuation) (by omega) h0
  have h2 := Source284ScratchPack.closed (3+(6+states))
    (Source284ScratchFlip.table (Source284ScratchFlipReturn.table continuation)) (by omega) h1
  have he : 133+(3+(6+states)) = 142+states := by omega
  rw [he] at h2
  exact h2

theorem description_eq (states : Nat) (continuation : Nat → Bool → Row) :
    description states continuation =
      Source284ScratchPack.description (3+(6+states))
        (Source284ScratchFlip.table (Source284ScratchFlipReturn.table continuation)) := by
  unfold description table Source284ScratchPack.description
  have he : 142+states = 133+(3+(6+states)) := by omega
  rw [he]

/-- The numeric source table performs the marker-flipping pass after packing. -/
theorem source_flip (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      ⟨certificate,2*scratch w (mark suffix),active 133⟩ (2*w.length+3) =
      ⟨4*push (2*certificate) w,suffix/4,active 136⟩ := by
  let c : Config := ⟨certificate,2*scratch w (mark suffix),some 0⟩
  have hvalid : Valid (142+states)
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 c))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := run_toSource (142+states) (table continuation) 1
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 c)))))
    (closed states continuation hn hv) hvalid (2*w.length+3)
  change Source284Relative.run (description states continuation)
    ⟨certificate,2*scratch w (mark suffix),active (8+(8+(16+(32+69))))⟩ _ = _ at hr
  have hs : 8+(8+(16+(32+69))) = 133 := by omega
  rw [hs] at hr
  rw [hr]
  change toSource (run (Source284InputSentinel.table
    (Source284ModePrefixScan.table (Source284ScratchTerminator.table
      (Source284PayloadLoop.table (Source284ScratchFlip.table (Source284ScratchFlipReturn.table continuation))))))
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 c))))) _) = _
  rw [Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    Source284ScratchTerminator.relocated_run,Source284ModePrefixReturn.relocated_run,
    Source284PayloadLoop.relocated_run,Source284ScratchFlip.scan_initial]
  rfl

/-- The reverse pass reaches the finite continuation with the full certificate
and the original head position restored. -/
theorem source_return (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      ⟨4*push (2*certificate) w,suffix/4,active 136⟩ (2*w.length+5) =
      ⟨certificate,2*flipped w (suffix/4),active 142⟩ := by
  let c : Config := ⟨4*push (2*certificate) w,suffix/4,some 0⟩
  have hvalid : Valid (142+states)
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 (shiftConfig 3 c)))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := run_toSource (142+states) (table continuation) 1
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 (shiftConfig 3 c))))))
    (closed states continuation hn hv) hvalid (2*w.length+5)
  change Source284Relative.run (description states continuation)
    ⟨4*push (2*certificate) w,suffix/4,active (8+(8+(16+(32+(69+3)))))⟩ _ = _ at hr
  have hs : 8+(8+(16+(32+(69+3)))) = 136 := by omega
  rw [hs] at hr
  rw [hr]
  change toSource (run (Source284InputSentinel.table
    (Source284ModePrefixScan.table (Source284ScratchTerminator.table
      (Source284PayloadLoop.table (Source284ScratchFlip.table (Source284ScratchFlipReturn.table continuation))))))
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 (shiftConfig 3 c)))))) _) = _
  rw [Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    Source284ScratchTerminator.relocated_run,Source284ModePrefixReturn.relocated_run,
    Source284PayloadLoop.relocated_run,Source284ScratchFlip.relocated_run,
    Source284ScratchFlipReturn.return_frame]
  rfl

/-- One fixed source table transforms every framed input to a scratch stream
which is self-delimiting in both directions, restores the certificate, and
reaches the supplied finite continuation within its exact quadratic cost. -/
theorem source_pipeline (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost w.length) =
      ⟨certificate,2*flipped w (suffix/4),active 142⟩ := by
  have hb := Source284ScratchFlipReturn.closed states continuation hn hv
  have hf := Source284ScratchFlip.closed (6+states) (Source284ScratchFlipReturn.table continuation) (by omega) hb
  have hp := Source284ScratchPack.source_pack_frame (3+(6+states))
    (Source284ScratchFlip.table (Source284ScratchFlipReturn.table continuation))
    w certificate suffix (by omega) hf
  rw [← description_eq] at hp
  have ht : totalCost w.length = Source284ScratchPack.totalCost w.length+
      ((2*w.length+3)+(2*w.length+5)) := by simp [totalCost]; omega
  rw [ht,Source284Relative.run_add_clock,hp,Source284Relative.run_add_clock]
  change Source284Relative.run (description states continuation)
    (Source284Relative.run (description states continuation)
      ⟨certificate,2*scratch w (mark suffix),active 133⟩ (2*w.length+3)) (2*w.length+5) = _
  rw [source_flip states continuation w certificate suffix hn hv,
    source_return states continuation w certificate suffix hn hv]

/-- Every numeric input reaches the continuation in finite time. Its
scratch stream has an executable decoder independent of high suffix data. -/
theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description states continuation)
        (Source284Relative.initial input certificate) (totalCost (Source284Parser.length input)) =
      ⟨certificate,2*flipped w (suffix/4),active 142⟩ ∧
      Source284ScratchFlipDecode.decode (flipped w (suffix/4)) = some w ∧
      Source284ScratchFlipDecode.inspections (flipped w (suffix/4)) = w.length+1 := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_,Source284ScratchFlipDecode.decode_flipped w _,
    Source284ScratchFlipDecode.inspections_flipped w _⟩
  rw [hlen,← hw]
  exact source_pipeline states continuation w certificate suffix hn hv

/-- The supplied finite continuation executes after the complete pipeline on
the actual resulting tape; the continuation time is charged separately. -/
theorem source_after_pipeline (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix clock : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.accepts (description states continuation) (encodeFrame w suffix) certificate
      (totalCost w.length+clock) =
    Source284Relative.accepts (encode states continuation 1) (2*flipped w (suffix/4)) certificate clock := by
  let c : Config := ⟨certificate,2*flipped w (suffix/4),some 0⟩
  have h0 : Valid states c := by
    intro q hq
    simp [c] at hq
    subst q
    exact hn
  have h1 : Valid (142+states)
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
        (shiftConfig 3 (shiftConfig 6 c))))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr1 := run_toSource (142+states) (table continuation) 1
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
      (shiftConfig 3 (shiftConfig 6 c))))))) (closed states continuation hn hv) h1 clock
  have hr0 := run_toSource states continuation 1 c hv h0 clock
  change Source284Relative.run (description states continuation)
    ⟨certificate,2*flipped w (suffix/4),active (8+(8+(16+(32+(69+(3+6))))))⟩ clock = _ at hr1
  have hs : 8+(8+(16+(32+(69+(3+6))))) = 142 := by omega
  rw [hs] at hr1
  change Source284Relative.run (encode states continuation 1)
    (Source284Relative.initial (2*flipped w (suffix/4)) certificate) clock = _ at hr0
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_pipeline states continuation w certificate suffix hn hv,hr1,hr0]
  change ((toSource (run (Source284InputSentinel.table
    (Source284ModePrefixScan.table (Source284ScratchTerminator.table
      (Source284PayloadLoop.table (Source284ScratchFlip.table (Source284ScratchFlipReturn.table continuation))))))
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
      (shiftConfig 3 (shiftConfig 6 c))))))) clock)).state == 0) =
        ((toSource (run continuation c clock)).state == 0)
  rw [Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    Source284ScratchTerminator.relocated_run,Source284ModePrefixReturn.relocated_run,
    Source284PayloadLoop.relocated_run,Source284ScratchFlip.relocated_run,
    Source284ScratchFlipReturn.relocated_run]
  cases h : (run continuation c clock).state <;>
    simp [toSource,shiftConfig,nextState,h,active]

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial 0 0) 24 = ⟨0,0,active 142⟩ := by
  simpa [encodeFrame,totalCost,Source284ScratchPack.totalCost,Source284PayloadLoop.cost,flipped] using
    source_pipeline states continuation [] 0 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial 295 7) 76 = ⟨7,278,active 142⟩ := by
  simpa [encodeFrame,totalCost,Source284ScratchPack.totalCost,Source284PayloadLoop.cost,flipped,bit] using
    source_pipeline states continuation [true,false] 7 9 hn hv

end Shared.Beeping.NPcoNP.Source284ScratchFlipPipeline
