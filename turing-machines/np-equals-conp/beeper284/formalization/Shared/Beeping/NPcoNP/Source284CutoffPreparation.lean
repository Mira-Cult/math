import Shared.Beeping.NPcoNP.Source284PreparedCutoff
import Shared.Beeping.NPcoNP.Source284PayloadSentinelPipeline
import Shared.Beeping.NPcoNP.Source284WitnessInputBound

/-! Compose the actual raw framed-witness preparation with the autonomous
unary cutoff comparator. The unary cutoff is still supplied on tape. Preparing
the full raw witness takes time depending on its length, not merely the cutoff;
this is useful for explicitly bounded certificate searches but does not give a
uniform input-only time bound for arbitrary huge certificate numbers. The
preparation consumes four ignored low suffix bits beyond the first delimiter. -/
set_option maxRecDepth 4096
namespace Shared.Beeping.NPcoNP.Source284CutoffPreparation

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def comparator (verifier : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284MatchLoop.table (Source284PreparedCutoff.router verifier)

def description (states : Nat) (verifier : Nat → Bool → Row) : Nat :=
  Source284PayloadSentinelPipeline.description (48+(4+states)) (comparator verifier)

theorem comparator_closed (states : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states verifier) :
    Closed (48+(4+states)) (comparator verifier) := by
  exact Source284MatchLoop.closed (4+states) (Source284PreparedCutoff.router verifier)
    (by omega) (Source284PreparedCutoff.router_closed states verifier hn hv)

/-- A raw framed witness is transformed by the actual source table while
the complete supplied unary tape half is left unchanged. -/
theorem source_prepare (states : Nat) (verifier : Nat → Bool → Row)
    (limit : Nat) (w : List Bool) (suffix otherHalf : Nat)
    (hn : 0 < states) (hv : Closed states verifier) :
    Source284Relative.run (description states verifier)
      (Source284Relative.initial (encodeFrame w suffix)
        (pairTape (List.replicate limit false) otherHalf))
      (Source284PayloadSentinelPipeline.totalCost w.length) =
      ⟨pairTape (List.replicate limit false) otherHalf,
        2*flipped (w++[false]) ((suffix/4)/4),active 155⟩ := by
  exact Source284PayloadSentinelPipeline.source_pipeline (48+(4+states)) (comparator verifier)
    w (pairTape (List.replicate limit false) otherHalf) suffix (by omega)
    (comparator_closed states verifier hn hv)

/-- After preparation, this same table has exactly the comparator's
acceptance behavior, with every preparation and comparison step charged. -/
theorem source_after (states : Nat) (verifier : Nat → Bool → Row)
    (limit : Nat) (w : List Bool) (suffix otherHalf clock : Nat)
    (hn : 0 < states) (hv : Closed states verifier) :
    Source284Relative.accepts (description states verifier) (encodeFrame w suffix)
      (pairTape (List.replicate limit false) otherHalf)
      (Source284PayloadSentinelPipeline.totalCost w.length+clock) =
    Source284Relative.accepts (Source284PreparedCutoff.description states verifier)
      (2*flipped (w++[false]) ((suffix/4)/4))
      (pairTape (List.replicate limit false) otherHalf) clock := by
  have h := Source284PayloadSentinelPipeline.source_after_pipeline
    (48+(4+states)) (comparator verifier) w
    (pairTape (List.replicate limit false) otherHalf) suffix clock (by omega)
    (comparator_closed states verifier hn hv)
  exact h

/-- Decoder rejection cannot be undone by dropping the ignored suffix bits
used for scratch space. The witness-length cutoff remains the original one. -/
theorem decoder_suffix_invariant (limit : Nat) (w : List Bool) (suffix : Nat) :
    (Source284WitnessWindow.decode limit (encodeFrame w suffix) = none) ↔
      (Source284WitnessWindow.decode limit (encodeFrame w ((suffix/4)/4)) = none) := by
  rw [Source284PreparedCutoff.decode_none_iff_length,Source284PreparedCutoff.decode_none_iff_length]

/-- Any overlong raw witness is rejected at every clock by one finite source
table, even if the supplied verifier itself would accept immediately. -/
theorem source_overlong_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (limit : Nat) (w : List Bool) (suffix otherHalf : Nat)
    (hn : 0 < states) (hv : Closed states verifier)
    (hover : Source284WitnessWindow.decode limit (encodeFrame w suffix) = none) :
    ∀ clock, Source284Relative.accepts (description states verifier) (encodeFrame w suffix)
      (pairTape (List.replicate limit false) otherHalf) clock = false := by
  have hover' := (decoder_suffix_invariant limit w suffix).mp hover
  have hafter : ∀ extra, Source284Relative.accepts (description states verifier) (encodeFrame w suffix)
      (pairTape (List.replicate limit false) otherHalf)
      (Source284PayloadSentinelPipeline.totalCost w.length+extra) = false := by
    intro extra
    rw [source_after states verifier limit w suffix otherHalf extra hn hv]
    exact Source284PreparedCutoff.prepared_overlong_never_accepts states verifier limit w
      ((suffix/4)/4) otherHalf hn hv hover' extra
  intro clock
  by_cases ht : Source284PayloadSentinelPipeline.totalCost w.length ≤ clock
  · have he : clock = Source284PayloadSentinelPipeline.totalCost w.length +
        (clock-Source284PayloadSentinelPipeline.totalCost w.length) := by omega
    rw [he]
    exact hafter _
  · apply Bool.eq_false_iff.mpr
    intro ha
    have hm := Source284Relative.accepts_clock_mono (description states verifier) (encodeFrame w suffix)
      (pairTape (List.replicate limit false) otherHalf) clock
      (Source284PayloadSentinelPipeline.totalCost w.length-clock) ha
    have he : clock+(Source284PayloadSentinelPipeline.totalCost w.length-clock) =
        Source284PayloadSentinelPipeline.totalCost w.length := by omega
    rw [he] at hm
    have hz := hafter 0
    simp only [Nat.add_zero] at hz
    rw [hz] at hm
    contradiction

/-- The paid raw-frame conversion is quadratic in the complete numeric
certificate's bit length. This does not bound that length by the main input. -/
theorem preparation_cost_le_size (input : Nat) :
    Source284PayloadSentinelPipeline.totalCost (Source284Parser.length input) ≤
      2*(Nat.size input)*(Nat.size input)+26*(Nat.size input)+36 := by
  have hm := Source284WitnessInputBound.parsed_length_le_size input
  have hp : Source284Parser.length input * Source284Parser.length input ≤
      Nat.size input * Nat.size input := Nat.mul_le_mul hm hm
  rw [Source284PayloadSentinelPipeline.totalCost_formula]
  nlinarith

/-- No framing hypothesis is required of the raw natural certificate:
virtual zero bits and arbitrary high data are handled by the source parser. -/
theorem source_raw_overlong_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (limit input otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (hover : Source284WitnessWindow.decode limit input = none) :
    ∀ clock, Source284Relative.accepts (description states verifier) input
      (pairTape (List.replicate limit false) otherHalf) clock = false := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  rw [← hw] at hover ⊢
  exact source_overlong_never_accepts states verifier limit w suffix otherHalf hn hv hover

/-- A source search restricted to numbers below `2^clock` pays a preparation
cost polynomial in that very clock, independent of discarded high suffixes. -/
theorem preparation_cost_le_clock (input clock : Nat) (hinput : input < 2^clock) :
    Source284PayloadSentinelPipeline.totalCost (Source284Parser.length input) ≤
      2*clock*clock+26*clock+36 := by
  have hs : Nat.size input ≤ clock := Nat.size_le.mpr hinput
  have hp : Nat.size input * Nat.size input ≤ clock*clock := Nat.mul_le_mul hs hs
  have hb := preparation_cost_le_size input
  nlinarith

/-- Once a valid tag has been checked and its two bits crossed, the raw
quotient is rejected exactly when the original tagged decoder rejects it.
The quotient is the supplied tape input here; this theorem does not claim
that the original tag-to-boundary adapter has already been built. -/
theorem source_tagged_overlong_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (limit certificate otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (htag : certificate%4 = 0)
    (hover : Source284TaggedWitnessCodec.decode limit certificate = none) :
    ∀ clock, Source284Relative.accepts (description states verifier) (certificate/4)
      (pairTape (List.replicate limit false) otherHalf) clock = false := by
  apply source_raw_overlong_never_accepts states verifier limit (certificate/4) otherHalf hn hv
  simpa [Source284TaggedWitnessCodec.decode,htag] using hover

/-- The same explicit clock bound applies to a tagged certificate after its
two tag bits have been crossed. -/
theorem tagged_preparation_cost_le_clock (certificate clock : Nat) (h : certificate < 2^clock) :
    Source284PayloadSentinelPipeline.totalCost (Source284Parser.length (certificate/4)) ≤
      2*clock*clock+26*clock+36 := by
  apply preparation_cost_le_clock
  have hd : certificate/4 ≤ certificate := Nat.div_le_self _ _
  omega

namespace Fixtures
open Source284PreparedCutoff.Fixtures (acceptImmediately accept_closed)

/-- Raw marker frame `7` contains two payload bits. A prepared bound of one
rejects it at every clock, even with an immediately accepting continuation. -/
example : ∀ clock, Source284Relative.accepts (description 1 acceptImmediately) 7 120 clock = false := by
  have h := source_raw_overlong_never_accepts 1 acceptImmediately 1 7 7
    (by omega) accept_closed (by decide +kernel)
  simpa [pairTape,Source284PayloadLoop.scratch,bit] using h

/-- Exact preparation cost and tape handoff at the two-bit boundary. -/
example : Source284Relative.run (description 1 acceptImmediately)
    (Source284Relative.initial 7 480) 96 = ⟨480,86,active 155⟩ := by
  have h := source_prepare 1 acceptImmediately 2 [true,false] 0 7 (by omega) accept_closed
  simpa [encodeFrame,pairTape,Source284PayloadLoop.scratch,flipped,bit,
    Source284PayloadSentinelPipeline.totalCost_formula] using h
/-- The exact-bound witness reaches and executes the supplied accepting
verifier through the same table after both paid stages. -/
theorem exact_bound_accepts : Source284Relative.accepts (description 1 acceptImmediately) 7 480 170 = true := by
  have hp := source_after 1 acceptImmediately 2 [true,false] 0 7 74 (by omega) accept_closed
  have he : 170 = Source284PayloadSentinelPipeline.totalCost ([true,false] : List Bool).length + 74 := by
    simp [Source284PayloadSentinelPipeline.totalCost_formula]
  have hc : Source284Relative.accepts (Source284PreparedCutoff.description 1 acceptImmediately) 86 480 74 = true := by
    have hcmp := Source284MatchLoopSource.equal_length 5 (Source284PreparedCutoff.router acceptImmediately)
      [true,false] 7 0 (by omega) (Source284PreparedCutoff.router_closed 1 acceptImmediately (by omega) accept_closed)
    have hcmp' : Source284Relative.run (Source284PreparedCutoff.description 1 acceptImmediately)
        (Source284Relative.initial 86 480) 72 = ⟨485,66,active 50⟩ := by
      simpa [Source284PreparedCutoff.description,Source284MatchLoopSource.compareCost,
        pairTape,Source284PayloadLoop.scratch,Source284PayloadMarkOne.zeros,flipped,bit] using hcmp
    have ht := Source284PreparedCutoff.source_good_turn 1 acceptImmediately 2 485 66
      (by omega) accept_closed (Or.inr rfl)
    change Source284Relative.run (Source284PreparedCutoff.description 1 acceptImmediately)
      ⟨485,66,active 50⟩ 1 = ⟨66,485,active 52⟩ at ht
    have hv := Source284PreparedCutoff.source_after_verifier 1 acceptImmediately 0 66 485 1
      (by omega) (by omega) accept_closed
    change Source284Relative.run (Source284PreparedCutoff.description 1 acceptImmediately)
      ⟨66,485,active 52⟩ 1 = _ at hv
    unfold Source284Relative.accepts
    rw [show 74 = 72+(1+1) by omega,Source284Relative.run_add_clock,hcmp',
      Source284Relative.run_add_clock,ht,hv]
    simp [acceptImmediately,run,step,
      Source284HardwireTable.shiftConfig,toSource,nextState]
  rw [he]
  simpa [encodeFrame,pairTape,Source284PayloadLoop.scratch,flipped,bit] using hp.trans hc
end Fixtures

end Shared.Beeping.NPcoNP.Source284CutoffPreparation
