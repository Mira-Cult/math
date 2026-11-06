import Shared.Beeping.NPcoNP.Source284OffsetResetAdapter
import Shared.Beeping.NPcoNP.Source284PrepareFrame

/-! Compile the decoded tagged-witness path through the paid mark reset and
existing finite scratch-frame normalizer. The high suffix is retained and a
canonical low window is proved; pair packing and physical refinement remain. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284OffsetFrameAdapter

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource shiftConfig_add)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284OffsetResetAdapter.table (Source284PrepareFrame.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (19+(80+states)) (table continuation) := by
  exact Source284OffsetResetAdapter.closed (80+states) (Source284PrepareFrame.table continuation)
    (by omega) (Source284PrepareFrame.closed states continuation hn hv)

/-- The 80-state finite frame converter, followed for arbitrary fuel. -/
theorem frame_then (continuation : Nat → Bool → Row) (w : List Bool) (left tail fuel : Nat) :
    run (Source284PrepareFrame.table continuation) ⟨left,2*flipped (w++[false]) tail,some 0⟩
      (10*w.length+21+fuel) =
    shiftConfig 80 (run continuation ⟨2*left,encodeFrame w (8*tail+1),some 0⟩ fuel) := by
  rw [Source284ScratchFlipReturn.run_add,Source284PrepareFrame.prepare]
  change run (Source284PrepareFrame.table continuation)
    ⟨2*left,encodeFrame w (8*tail+1),some (80+0)⟩ fuel = _
  rw [Source284PrepareFrame.continuation_run]
  rw [shiftConfig_add,shiftConfig_add,shiftConfig_add]

/-- Even with an unbounded retained suffix, the first delimiter-and-sentinel
window is exactly the canonical frame of the witness. -/
theorem frame_low_window (w : List Bool) (tail : Nat) :
    encodeFrame w (8*tail+1) % 4^(w.length+1) = encodeFrame w 1 := by
  simpa [show 2*(4*tail) = 8*tail by omega] using Source284NormalizedWindow.normalized_mod w (4*tail)

/-- A fixed-width bit reader sees the canonical frame, not the retained
high suffix. This equality concerns the finite window, not the whole tape. -/
theorem frame_low_bits (w : List Bool) (tail : Nat) :
    Source284CanonicalPairWindow.window (2*w.length+2) (encodeFrame w (8*tail+1)) =
      Source284Parser.frameBits w [true] := by
  apply Source284CanonicalPairWindow.same_length_value_injective
  · rw [Source284CanonicalPairWindow.window_length,Source284WitnessWindow.frame_length]
  · rw [Source284CanonicalPairWindow.window_value]
    have hp : 2^(2*w.length+2) = 4^(w.length+1) := by
      have he : 2*w.length+2 = 2*(w.length+1) := by omega
      rw [he,Nat.pow_mul]
    rw [hp,frame_low_window]
    simpa [Shared.Codes.BitNumeralCompare.value] using Source284Parser.encodeFrame_eq_value w [true]

/-- Actual finite source execution reaches a frame for the decoded witness,
then follows the supplied finite continuation. All reset and conversion
steps are paid. The suffix is retained and exposed, not magically erased. -/
theorem decoded_frame_then (states : Nat) (continuation : Nat → Bool → Row)
    (limit certificate otherHalf : Nat) (w : List Bool)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ suffix, certificate = 4*encodeFrame w suffix ∧
      encodeFrame w (8*((suffix/4)/4)+1) % 4^(w.length+1) = encodeFrame w 1 ∧
      ∀ fuel, Source284Relative.run (Source284OffsetTagged.description (19+(80+states)) (table continuation))
        (Source284Relative.initial certificate (pairTape (List.replicate limit false) otherHalf))
        (4+(Source284PayloadSentinelPipeline.totalCost w.length+
          (Source284OffsetMatch.compareCost w.length+(1+
            ((1+((4*(limit+1)+6)+(4*w.length+12)))+(10*w.length+21+fuel)))))) =
      lift 311 (Source284Relative.run (encode states continuation 1)
        ⟨2*pairTape (List.replicate (limit+1) false) otherHalf,
          encodeFrame w (8*((suffix/4)/4)+1),active 0⟩ fuel) := by
  have hc := Source284PrepareFrame.closed states continuation hn hv
  obtain ⟨suffix,hcert,hr⟩ := Source284OffsetResetAdapter.decoded_reset_then
    (80+states) (Source284PrepareFrame.table continuation) limit certificate otherHalf w (by omega) hc hdec
  refine ⟨suffix,hcert,frame_low_window w ((suffix/4)/4),?_⟩
  intro fuel
  let left := pairTape (List.replicate (limit+1) false) otherHalf
  let tail := (suffix/4)/4
  have hr' := hr (10*w.length+21+fuel)
  change Source284Relative.run _ _ _ = lift 231
    (Source284Relative.run (encode (80+states) (Source284PrepareFrame.table continuation) 1)
      ⟨left,2*flipped (w++[false]) tail,active 0⟩ (10*w.length+21+fuel)) at hr'
  let c : Config := ⟨left,2*flipped (w++[false]) tail,some 0⟩
  have hvalid : Valid (80+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have hv0 := run_toSource (80+states) (Source284PrepareFrame.table continuation) 1 c hc hvalid (10*w.length+21+fuel)
  change Source284Relative.run (encode (80+states) (Source284PrepareFrame.table continuation) 1)
      ⟨left,2*flipped (w++[false]) tail,active 0⟩ _ = _ at hv0
  rw [hv0,frame_then] at hr'
  let c' : Config := ⟨2*left,encodeFrame w (8*tail+1),some 0⟩
  have hvalid' : Valid states c' := by intro q hq; simp [c'] at hq; subst q; exact hn
  have hv1 := run_toSource states continuation 1 c' hv hvalid' fuel
  change Source284Relative.run (encode states continuation 1)
      ⟨2*left,encodeFrame w (8*tail+1),active 0⟩ fuel = _ at hv1
  rw [← lift_toSource,Source284SourceRelocation.lift_add,← hv1] at hr'
  exact hr'

namespace Fixtures

/-- A nonzero high suffix does not alter the bounded canonical witness frame. -/
example : Source284CanonicalPairWindow.window 4 (encodeFrame [false] (8*7+1)) =
    [true,false,false,true] := by
  simpa [Source284Parser.frameBits] using frame_low_bits [false] 7

/-- The empty witness has the two-bit delimiter/sentinel frame. -/
example : Source284CanonicalPairWindow.window 2 (encodeFrame [] (8*91+1)) =
    [false,true] := by
  simpa [Source284Parser.frameBits] using frame_low_bits [] 91

end Fixtures

end Shared.Beeping.NPcoNP.Source284OffsetFrameAdapter
