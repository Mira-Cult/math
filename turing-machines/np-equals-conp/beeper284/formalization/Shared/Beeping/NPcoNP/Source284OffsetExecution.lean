import Shared.Beeping.NPcoNP.Source284SourceRelocation
import Shared.Beeping.NPcoNP.Source284OffsetTagged

/-! Exact operational composition of the tag/mark prefix, raw witness
conversion, and finite unary cutoff comparator. The resulting state offsets
are logical source states, not physical beeper states. The unary cutoff must
already be positioned on the supplied tape half. -/
set_option maxRecDepth 4096
namespace Shared.Beeping.NPcoNP.Source284OffsetExecution

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource shiftConfig_add)

/-- This is full configuration equality, including the absorbing state, not
merely agreement on whether a clocked run accepts. -/
theorem source_run_after_tag (states : Nat) (verifier : Nat → Bool → Row)
    (limit certificate otherHalf clock : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (htag : certificate%4 = 0) :
    Source284Relative.run (Source284OffsetTagged.description states verifier)
      (Source284Relative.initial certificate (pairTape (List.replicate limit false) otherHalf)) (4+clock) =
    lift 5 (Source284Relative.run (Source284CutoffPreparation.description states verifier)
      (Source284Relative.initial (certificate/4) (pairTape (true::List.replicate limit false) otherHalf)) clock) := by
  let c : Config := ⟨pairTape (true::List.replicate limit false) otherHalf,certificate/4,some 0⟩
  have hv0 : Valid (Source284OffsetTagged.rawStates states) c := by
    intro q hq; simp [c] at hq; subst q; simp [Source284OffsetTagged.rawStates,Source284PositiveTaggedCutoff.rawStates]
  have hv1 : Valid (Source284OffsetTagged.goodStates states) (shiftConfig 2 c) := by
    intro q hq; simp [c,shiftConfig] at hq; subst q; simp [Source284OffsetTagged.goodStates,Source284OffsetTagged.rawStates,Source284PositiveTaggedCutoff.rawStates]
  have hv2 : Valid (3+Source284OffsetTagged.goodStates states+1) (shiftConfig 3 (shiftConfig 2 c)) := by
    intro q hq; simp [c,shiftConfig] at hq; subst q
    simp [Source284OffsetTagged.goodStates,Source284OffsetTagged.rawStates,Source284PositiveTaggedCutoff.rawStates] <;> omega
  have hr0 := run_toSource (Source284OffsetTagged.rawStates states) (Source284OffsetTagged.rawTable verifier) 1 c
    (Source284PositiveTaggedCutoff.raw_closed states verifier hn hv) hv0 clock
  have hr1 := run_toSource (3+Source284OffsetTagged.goodStates states+1) (Source284OffsetTagged.table states verifier) 1
    (shiftConfig 3 (shiftConfig 2 c)) (Source284OffsetTagged.table_closed states verifier hn hv) hv2 clock
  change Source284Relative.run (encode (Source284PositiveTaggedCutoff.rawStates states)
    (Source284PositiveTaggedCutoff.rawTable verifier) 1) (toSource c) clock = _ at hr0
  rw [Source284PositiveTaggedCutoff.raw_description] at hr0
  change Source284Relative.run (Source284CutoffPreparation.description states verifier)
    (Source284Relative.initial (certificate/4) (pairTape (true::List.replicate limit false) otherHalf)) clock = _ at hr0
  change Source284Relative.run (Source284OffsetTagged.description states verifier)
    ⟨pairTape (true::List.replicate limit false) otherHalf,certificate/4,active 5⟩ clock =
    toSource (run (Source284TaggedHandoff.table (Source284OffsetTagged.goodStates states)
      (Source284OffsetTagged.goodTable verifier) Source284TaggedHandoff.rejectTable)
      (shiftConfig 3 (shiftConfig 2 c)) clock) at hr1
  rw [Source284TaggedHandoff.good_run (Source284OffsetTagged.goodStates states)
    (Source284OffsetTagged.goodTable verifier) Source284TaggedHandoff.rejectTable _
    (Source284OffsetTagged.good_closed states verifier hn hv) hv1] at hr1
  change Source284Relative.run (Source284OffsetTagged.description states verifier) _ _ =
    toSource (shiftConfig 3 (run (Source284OffsetTagged.markTable (Source284OffsetTagged.rawTable verifier))
      (shiftConfig 2 c) clock)) at hr1
  rw [Source284OffsetTagged.mark_relocated_run] at hr1
  rw [Source284Relative.run_add_clock,
    Source284OffsetTagged.source_tag_and_mark states verifier limit certificate otherHalf hn hv htag,hr1,hr0,
    lift_toSource,shiftConfig_add]

/-- The full paid source prefix reaches the offset comparator with exact
configuration correspondence for every subsequent clock. -/
theorem source_run_after_preparation (states : Nat) (verifier : Nat → Bool → Row)
    (limit certificate otherHalf : Nat) (w : List Bool) (suffix clock : Nat)
    (hn : 0 < states) (hv : Closed states verifier) (htag : certificate%4 = 0)
    (hw : encodeFrame w suffix = certificate/4) :
    Source284Relative.run (Source284OffsetTagged.description states verifier)
      (Source284Relative.initial certificate (pairTape (List.replicate limit false) otherHalf))
      (4+(Source284PayloadSentinelPipeline.totalCost w.length+clock)) =
    lift 160 (Source284Relative.run (Source284PreparedCutoff.description states verifier)
      (Source284Relative.initial (2*flipped (w++[false]) ((suffix/4)/4))
        (pairTape (true::List.replicate limit false) otherHalf)) clock) := by
  rw [source_run_after_tag states verifier limit certificate otherHalf _ hn hv htag,← hw]
  have hr := Source284SourceRelocation.source_run_after_pipeline
    (48+(4+states)) (Source284CutoffPreparation.comparator verifier) w
    (pairTape (true::List.replicate limit false) otherHalf) suffix clock (by omega)
    (Source284CutoffPreparation.comparator_closed states verifier hn hv)
  change Source284Relative.run (Source284CutoffPreparation.description states verifier)
    (Source284Relative.initial (encodeFrame w suffix) (pairTape (true::List.replicate limit false) otherHalf))
    (Source284PayloadSentinelPipeline.totalCost w.length+clock) =
    lift 155 (Source284Relative.run (Source284PreparedCutoff.description states verifier)
      (Source284Relative.initial (2*flipped (w++[false]) ((suffix/4)/4))
        (pairTape (true::List.replicate limit false) otherHalf)) clock) at hr
  rw [hr,Source284SourceRelocation.lift_add]

/-- Every valid tag reaches an exact cutoff-classification state after a
finite, explicitly bounded source run. All retained tape data in the result
are the actual comparator output, not a preloaded configuration. -/
theorem source_classification_progress (states : Nat) (verifier : Nat → Bool → Row)
    (limit certificate otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (htag : certificate%4 = 0) :
    ∃ (w : List Bool) (suffix left right mode t : Nat),
      encodeFrame w suffix = certificate/4 ∧
      t ≤ 4+Source284PayloadSentinelPipeline.totalCost (Source284Parser.length (certificate/4))+
        4*limit*limit+24*limit+20 ∧
      Source284Relative.run (Source284OffsetTagged.description states verifier)
        (Source284Relative.initial certificate (pairTape (List.replicate limit false) otherHalf)) t =
        ⟨left,right,active (208+mode)⟩ ∧
      (mode = 1 ↔ Source284TaggedWitnessCodec.decode limit certificate = none) ∧
      (mode = 0 ↔ w.length < limit) ∧ (mode = 2 ↔ limit = w.length) := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective (certificate/4)
  have hlen : Source284Parser.length (certificate/4) = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  obtain ⟨left,right,mode,t,ht,hr,hbad,h0,h2⟩ :=
    Source284OffsetMatch.source_decoder_classification states verifier limit w ((suffix/4)/4) otherHalf hn hv
  refine ⟨w,suffix,left,right,mode,4+(Source284PayloadSentinelPipeline.totalCost w.length+t),hw,?_,?_,?_,h0,h2⟩
  · rw [hlen]
    omega
  · rw [source_run_after_preparation states verifier limit certificate otherHalf w suffix t hn hv htag hw,hr,
      Source284SourceRelocation.lift_active]
    simp [active] <;> omega
  · have hdec : (Source284TaggedWitnessCodec.decode limit certificate = none) ↔
        (Source284WitnessWindow.decode limit (encodeFrame w ((suffix/4)/4)) = none) := by
      simp only [Source284TaggedWitnessCodec.decode,htag,↓reduceIte,← hw]
      exact Source284CutoffPreparation.decoder_suffix_invariant limit w suffix
    rw [hdec]
    exact hbad

/-- Every decoder-valid tagged witness reaches the supplied verifier after a
bounded positive number of source steps, then follows that verifier exactly
(up to the proved source-state relocation) for every subsequent clock. The
verifier is not assumed to terminate. -/
theorem source_within_verifier_progress (states : Nat) (verifier : Nat → Bool → Row)
    (limit certificate otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (hwithin : Source284TaggedWitnessCodec.decode limit certificate ≠ none) :
    ∃ (left right t : Nat),
      t ≤ 4+Source284PayloadSentinelPipeline.totalCost (Source284Parser.length (certificate/4))+
        4*limit*limit+24*limit+21 ∧
      ∀ fuel, Source284Relative.run (Source284OffsetTagged.description states verifier)
        (Source284Relative.initial certificate (pairTape (List.replicate limit false) otherHalf)) (t+fuel) =
      lift 212 (Source284Relative.run (encode states verifier 1) ⟨right,left,active 0⟩ fuel) := by
  have htag : certificate%4 = 0 := by
    by_contra h
    apply hwithin
    simp [Source284TaggedWitnessCodec.decode,h]
  have hraw : Source284WitnessWindow.decode limit (certificate/4) ≠ none := by
    simpa [Source284TaggedWitnessCodec.decode,htag] using hwithin
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective (certificate/4)
  have hlen : Source284Parser.length (certificate/4) = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  have hle : w.length ≤ limit := by
    by_contra h
    apply hraw
    rw [← hw,Source284PreparedCutoff.decode_none_iff_length]
    omega
  obtain ⟨left,right,mode,t,ht,hr,_,h0,h2⟩ :=
    Source284OffsetMatch.source_decoder_classification states verifier limit w ((suffix/4)/4) otherHalf hn hv
  have hm : mode = 0 ∨ mode = 2 := by
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact Or.inl (h0.mpr h)
    · exact Or.inr (h2.mpr h.symm)
  refine ⟨left,right,4+(Source284PayloadSentinelPipeline.totalCost w.length+(t+1)),?_,?_⟩
  · rw [hlen]
    omega
  · intro fuel
    let c : Config := ⟨right,left,some 0⟩
    have hc : Valid states c := by intro q hq; simp [c] at hq; subst q; exact hn
    have hv0 := run_toSource states verifier 1 c hv hc fuel
    change Source284Relative.run (encode states verifier 1) ⟨right,left,active 0⟩ fuel = _ at hv0
    have hv1 := Source284PreparedCutoff.source_after_verifier states verifier 0 right left fuel hn (by omega) hv
    change Source284Relative.run (Source284PreparedCutoff.description states verifier)
      ⟨right,left,active 52⟩ fuel = _ at hv1
    have htime : (4+(Source284PayloadSentinelPipeline.totalCost w.length+(t+1)))+fuel =
        4+(Source284PayloadSentinelPipeline.totalCost w.length+(t+(1+fuel))) := by omega
    rw [htime,source_run_after_preparation states verifier limit certificate otherHalf w suffix _ hn hv htag hw,
      Source284Relative.run_add_clock,hr,Source284Relative.run_add_clock,
      Source284PreparedCutoff.source_good_turn states verifier mode left right hn hv hm,hv1,hv0]
    rw [shiftConfig_add, ← lift_toSource, Source284SourceRelocation.lift_add]

end Shared.Beeping.NPcoNP.Source284OffsetExecution
