import Shared.Beeping.NPcoNP.Source284OffsetExecution

/-! Exact tapes at the verifier handoff for within-bound framed witnesses.
The high suffix is explicitly retained; this is not yet a canonical pair or
an event-preserving refinement to the physical machine. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284OffsetExactHandoff

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource shiftConfig_add)

/-- The comparator has marked the tag pair and one pair per witness bit.
On the strict branch it also marks the first unused bound pair. -/
def boundTokens (limit : Nat) (w : List Bool) : List Bool :=
  if w.length = limit then List.replicate (1+w.length) true
  else List.replicate (1+w.length) true ++ true :: List.replicate (limit-(w.length+1)) false

def mode (limit : Nat) (w : List Bool) : Nat := if w.length = limit then 2 else 0

/-- For an in-bound framed witness, the comparator exposes the exact tape
contents, with its finite time determined solely by the witness length. -/
theorem source_compare_exact (states : Nat) (verifier : Nat → Bool → Row)
    (limit : Nat) (w : List Bool) (otherHalf tail : Nat)
    (hn : 0 < states) (hv : Closed states verifier) (hw : w.length ≤ limit) :
    Source284Relative.run (Source284PreparedCutoff.description states verifier)
      (Source284Relative.initial (2*flipped (w++[false]) tail)
        (pairTape (true::List.replicate limit false) otherHalf))
      (Source284OffsetMatch.compareCost w.length) =
    ⟨pairTape (boundTokens limit w) otherHalf, 2*zeros w (flipped [false] tail),
      active (48+mode limit w)⟩ := by
  let cont := Source284PreparedCutoff.router verifier
  have hc := Source284PreparedCutoff.router_closed states verifier hn hv
  have hsource : ∀ left right clock,
      Source284Relative.run (Source284PreparedCutoff.description states verifier)
        (Source284Relative.initial right left) clock =
      toSource (run (Source284MatchLoop.table cont) ⟨left,right,some 0⟩ clock) := by
    intro left right clock
    exact Source284MatchLoopSource.source_run (4+states) cont left right clock (by omega) hc
  by_cases he : w.length = limit
  · subst limit
    rw [hsource,Source284OffsetMatch.equal_length]
    simp [boundTokens,mode,toSource,nextState,active]
  · have heq : w.length+1+(limit-(w.length+1)) = limit := by omega
    have hr := Source284OffsetMatch.more_tokens cont w (limit-(w.length+1)) otherHalf tail
    rw [heq] at hr
    rw [hsource,hr]
    simp [boundTokens,mode,he,toSource,nextState,active]

/-- An in-bound frame reaches the supplied verifier with exact tape halves
and follows it for every further clock. The suffix is not silently discarded. -/
theorem source_verifier_exact (states : Nat) (verifier : Nat → Bool → Row)
    (limit : Nat) (w : List Bool) (suffix otherHalf fuel : Nat)
    (hn : 0 < states) (hv : Closed states verifier) (hw : w.length ≤ limit) :
    Source284Relative.run (Source284OffsetTagged.description states verifier)
      (Source284Relative.initial (4*encodeFrame w suffix)
        (pairTape (List.replicate limit false) otherHalf))
      (4+(Source284PayloadSentinelPipeline.totalCost w.length+
        (Source284OffsetMatch.compareCost w.length+(1+fuel)))) =
    lift 212 (Source284Relative.run (encode states verifier 1)
      ⟨2*zeros w (flipped [false] ((suffix/4)/4)),
        pairTape (boundTokens limit w) otherHalf,active 0⟩ fuel) := by
  have htag : (4*encodeFrame w suffix)%4 = 0 := by omega
  have hframe : encodeFrame w suffix = (4*encodeFrame w suffix)/4 := by omega
  have hm : mode limit w = 0 ∨ mode limit w = 2 := by
    simp only [mode]
    split <;> simp
  let left := pairTape (boundTokens limit w) otherHalf
  let right := 2*zeros w (flipped [false] ((suffix/4)/4))
  let c : Config := ⟨right,left,some 0⟩
  have hc : Valid states c := by intro q hq; simp [c] at hq; subst q; exact hn
  have hv0 := run_toSource states verifier 1 c hv hc fuel
  change Source284Relative.run (encode states verifier 1) ⟨right,left,active 0⟩ fuel = _ at hv0
  have hv1 := Source284PreparedCutoff.source_after_verifier states verifier 0 right left fuel hn (by omega) hv
  change Source284Relative.run (Source284PreparedCutoff.description states verifier)
    ⟨right,left,active 52⟩ fuel = _ at hv1
  rw [Source284OffsetExecution.source_run_after_preparation states verifier limit
    (4*encodeFrame w suffix) otherHalf w suffix _ hn hv htag hframe,
    Source284Relative.run_add_clock,
    source_compare_exact states verifier limit w otherHalf ((suffix/4)/4) hn hv hw,
    Source284Relative.run_add_clock,
    Source284PreparedCutoff.source_good_turn states verifier (mode limit w) left right hn hv hm,hv1,hv0]
  rw [shiftConfig_add,← lift_toSource,Source284SourceRelocation.lift_add]

/-- The executable canonical tagged encoding uses suffix one. -/
theorem canonical_tagged_frame (w : List Bool) :
    Source284TaggedWitnessCodec.encode w = 4*encodeFrame w 1 := by
  unfold Source284TaggedWitnessCodec.encode Source284WitnessWindow.encode
  rw [← Source284Parser.encodeFrame_eq_value]
  rfl

/-- Canonical encodings have no residual high suffix at handoff. Their
actual bounded decoder returns the supplied list, and the verifier starts on
the explicitly displayed marked tape halves. -/
theorem canonical_verifier_exact (states : Nat) (verifier : Nat → Bool → Row)
    (limit : Nat) (w : List Bool) (otherHalf fuel : Nat)
    (hn : 0 < states) (hv : Closed states verifier) (hw : w.length ≤ limit) :
    Source284TaggedWitnessCodec.decode limit (Source284TaggedWitnessCodec.encode w) = some w ∧
    Source284Relative.run (Source284OffsetTagged.description states verifier)
      (Source284Relative.initial (Source284TaggedWitnessCodec.encode w)
        (pairTape (List.replicate limit false) otherHalf))
      (4+(Source284PayloadSentinelPipeline.totalCost w.length+
        (Source284OffsetMatch.compareCost w.length+(1+fuel)))) =
    lift 212 (Source284Relative.run (encode states verifier 1)
      ⟨2*zeros w (flipped [false] 0),pairTape (boundTokens limit w) otherHalf,active 0⟩ fuel) := by
  refine ⟨Source284TaggedWitnessCodec.decode_encode limit w hw, ?_⟩
  rw [canonical_tagged_frame]
  simpa using source_verifier_exact states verifier limit w 1 otherHalf fuel hn hv hw

/-- High aliases can decode to the same empty list while leaving different
verifier-entry data. A wrapper must account for this data rather than assume
that successful decoding normalizes the tape. -/
example : Source284TaggedWitnessCodec.decode 0 8 = some [] ∧
    Source284TaggedWitnessCodec.decode 0 136 = some [] ∧
    2*zeros [] (flipped [false] ((1/4)/4)) = 4 ∧
    2*zeros [] (flipped [false] ((17/4)/4)) = 36 := by
  decide +kernel

end Shared.Beeping.NPcoNP.Source284OffsetExactHandoff
