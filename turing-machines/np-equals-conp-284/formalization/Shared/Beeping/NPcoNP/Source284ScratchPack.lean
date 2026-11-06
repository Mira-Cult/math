import Shared.Beeping.NPcoNP.Source284ScratchTerminator
import Shared.Beeping.NPcoNP.Source284ScratchDecode

/-! Compose the paid terminator installation with the fixed quadratic payload
loop. The result is an executable finite source table with a self-delimited
scratch stream, not yet the canonical pair or witness-window loader. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchPack

set_option maxHeartbeats 1000000

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284PayloadLoop (scratch cost)
open Shared.Beeping.NPcoNP.Source284ScratchTerminator (mark)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284InputSentinel.table
    (Source284ModePrefixScan.table
      (Source284ScratchTerminator.table (Source284PayloadLoop.table continuation)))

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  encode (133+states) (table continuation) 1

def totalCost (n : Nat) : Nat := (4*n+14)+cost n

theorem totalCost_formula (n : Nat) : totalCost n = 2*n*n+18*n+16 := by
  simp [totalCost,cost]
  ring

theorem totalCost_positive (n : Nat) : 0 < totalCost n := by
  rw [totalCost_formula]
  omega

/-- The source encoding allocates 133 logical prefix states, plus the
continuation; each logical state contributes two encoded row records. -/
theorem record_count (states : Nat) (continuation : Nat → Bool → Row) :
    (records (133+states) (table continuation)).length = 2*(133+states) := by
  simp [records]

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (133+states) (table continuation) := by
  have h0 := Source284PayloadLoop.closed states continuation hn hv
  have h1 := Source284ScratchTerminator.closed (69+states) (Source284PayloadLoop.table continuation)
    (by omega) h0
  have h2 := Source284ModePrefixScan.closed (16+(32+(69+states)))
    (Source284ScratchTerminator.table (Source284PayloadLoop.table continuation)) (by omega) h1
  have h3 := Source284InputSentinel.closed (8+(16+(32+(69+states))))
    (Source284ModePrefixScan.table (Source284ScratchTerminator.table (Source284PayloadLoop.table continuation)))
    (by omega) h2
  have he : 8+(8+(16+(32+(69+states)))) = 133+states := by omega
  rw [he] at h3
  exact h3

theorem description_eq (states : Nat) (continuation : Nat → Bool → Row) :
    description states continuation =
      Source284InputSentinel.description (8+(16+(32+(69+states))))
        (Source284ModePrefixScan.table
          (Source284ScratchTerminator.table (Source284PayloadLoop.table continuation))) := by
  unfold description table Source284InputSentinel.description
  have he : 133+states = 8+(8+(16+(32+(69+states)))) := by omega
  rw [he]

/-- After the marked frame has been prepared, the same numeric source table
executes the complete payload-to-scratch loop. -/
theorem source_after_mark (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      ⟨certificate,encodeFrame w (mark suffix),active 64⟩ (cost w.length) =
      ⟨certificate,encodeFrame [] (scratch w (mark suffix)),active 133⟩ := by
  let c : Config := ⟨certificate,encodeFrame w (mark suffix),some 0⟩
  have hvalid : Valid (133+states)
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 c)))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := run_toSource (133+states) (table continuation) 1
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 c))))
    (closed states continuation hn hv) hvalid (cost w.length)
  change Source284Relative.run (description states continuation)
    ⟨certificate,encodeFrame w (mark suffix),active (8+(8+(16+32)))⟩ _ = _ at hr
  have hs : 8+(8+(16+32)) = 64 := by omega
  rw [hs] at hr
  rw [hr]
  change toSource (run (Source284InputSentinel.table
    (Source284ModePrefixScan.table (Source284ScratchTerminator.table
      (Source284PayloadLoop.table continuation))))
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 c)))) _) = _
  rw [Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    Source284ScratchTerminator.relocated_run,Source284ModePrefixReturn.relocated_run,
    Source284PayloadLoop.loop_frame]
  rfl

/-- A single finite source program sets its own delimiter and moves every
payload bit into the scratch stream. No input length or program is preloaded. -/
theorem source_pack_frame (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost w.length) =
      ⟨certificate,encodeFrame [] (scratch w (mark suffix)),active 133⟩ := by
  have hc := Source284PayloadLoop.closed states continuation hn hv
  have hmark := Source284ScratchTerminator.source_mark (69+states) (Source284PayloadLoop.table continuation)
    w certificate suffix (by omega) hc
  rw [← description_eq] at hmark
  rw [totalCost,Source284Relative.run_add_clock,hmark,source_after_mark states continuation w certificate suffix hn hv]

/-- This positive finite execution applies to every raw numeric source input;
the original ignored suffix may contain arbitrary data. -/
theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description states continuation)
        (Source284Relative.initial input certificate) (totalCost (Source284Parser.length input)) =
      ⟨certificate,encodeFrame [] (scratch w (mark suffix)),active 133⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [hlen,← hw]
  exact source_pack_frame states continuation w certificate suffix hn hv

/-- The constructed scratch stream decodes to exactly the input payload,
regardless of the original ignored suffix. The executable mathematical
decoder inspects one block per payload bit and one terminator block. -/
theorem output_decodes (w : List Bool) (suffix : Nat) :
    Source284ScratchDecode.decode (scratch w (mark suffix)) = some w ∧
      Source284ScratchDecode.inspections (scratch w (mark suffix)) = w.length+1 :=
  ⟨Source284ScratchDecode.decode_marked w suffix,
    Source284ScratchDecode.inspections_marked w suffix⟩

/-- Every raw input is packed in a fixed finite source execution and the
resulting mathematical scratch decoder recovers its payload. The decoder is
not claimed to be part of that source table. -/
theorem source_packs_decodable (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description states continuation)
        (Source284Relative.initial input certificate) (totalCost (Source284Parser.length input)) =
      ⟨certificate,encodeFrame [] (scratch w (mark suffix)),active 133⟩ ∧
      Source284ScratchDecode.decode (scratch w (mark suffix)) = some w ∧
      Source284ScratchDecode.inspections (scratch w (mark suffix)) = w.length+1 := by
  obtain ⟨w,suffix,hw,hlen,hr⟩ := source_total_progress states continuation input certificate hn hv
  exact ⟨w,suffix,hw,hlen,hr,(output_decodes w suffix).1,(output_decodes w suffix).2⟩

/-- The finite continuation receives the produced scratch tape in the same
source execution, with its subsequent clock added to the setup cost. -/
theorem source_after_pack (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix clock : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.accepts (description states continuation) (encodeFrame w suffix) certificate
      (totalCost w.length+clock) =
    Source284Relative.accepts (encode states continuation 1)
      (encodeFrame [] (scratch w (mark suffix))) certificate clock := by
  let c : Config := ⟨certificate,encodeFrame [] (scratch w (mark suffix)),some 0⟩
  have h0 : Valid states c := by
    intro q hq
    simp [c] at hq
    subst q
    exact hn
  have h1 : Valid (133+states)
      (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 c))))) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr1 := run_toSource (133+states) (table continuation) 1
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 c)))))
    (closed states continuation hn hv) h1 clock
  have hr0 := run_toSource states continuation 1 c hv h0 clock
  change Source284Relative.run (description states continuation)
    ⟨certificate,encodeFrame [] (scratch w (mark suffix)),active (8+(8+(16+(32+69))))⟩ clock = _ at hr1
  have hs : 8+(8+(16+(32+69))) = 133 := by omega
  rw [hs] at hr1
  change Source284Relative.run (encode states continuation 1)
    (Source284Relative.initial (encodeFrame [] (scratch w (mark suffix))) certificate) clock = _ at hr0
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_pack_frame states continuation w certificate suffix hn hv,hr1,hr0]
  change ((toSource (run (Source284InputSentinel.table
    (Source284ModePrefixScan.table (Source284ScratchTerminator.table
      (Source284PayloadLoop.table continuation))))
    (shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69 c))))) clock)).state == 0) =
      ((toSource (run continuation c clock)).state == 0)
  rw [Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    Source284ScratchTerminator.relocated_run,Source284ModePrefixReturn.relocated_run,
    Source284PayloadLoop.relocated_run]
  cases h : (run continuation c clock).state <;>
    simp [toSource,shiftConfig,nextState,h,active]

-- The original ignored suffix and low certificate bits are nonzero in the
-- second fixture; both examples use the universal finite-execution proof.
example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial 0 0) 16 = ⟨0,4,active 133⟩ := by
  simpa [encodeFrame,totalCost,cost,scratch,mark] using
    source_pack_frame states continuation [] 0 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial 295 7) 60 = ⟨7,322,active 133⟩ := by
  simpa [encodeFrame,totalCost,cost,scratch,mark,bit] using
    source_pack_frame states continuation [true,false] 7 9 hn hv

end Shared.Beeping.NPcoNP.Source284ScratchPack
