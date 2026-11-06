import Shared.Beeping.NPcoNP.Source284PositiveTaggedCutoff

/-! The existing comparator with unequal already-marked prefixes. One extra
marked unary pair can account for the two crossed tag cells without enlarging
the witness cutoff. This file proves finite comparison on prepared tapes;
constructing and connecting those tapes remains a separate obligation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284OffsetMatch

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284MatchLoop (table)

def repeatCost (k p n : Nat) : Nat := n*(4*k+4*p+12+4*n)

theorem repeatCost_succ (k p n : Nat) :
    repeatCost k p (n+1) = (4*k+6+(4*p+10))+repeatCost (k+1) (p+1) n := by
  unfold repeatCost
  ring

/-- The actual finite comparator matches arbitrarily many pairs when the
numbers of already-marked unary and payload pairs need not agree. -/
theorem repeat_pairs (continuation : Nat → Bool → Row) (k : Nat) (tokens xs ys rest : List Bool)
    (certificate tail : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate k true ++ List.replicate ys.length false ++ tokens) certificate,
        2*zeros xs (flipped (ys++rest++[false]) tail),some 0⟩ (repeatCost k xs.length ys.length) =
    ⟨pairTape (List.replicate (k+ys.length) true ++ tokens) certificate,
      2*zeros (xs++ys) (flipped (rest++[false]) tail),some 0⟩ := by
  induction ys generalizing k xs with
  | nil => simp [repeatCost,run]
  | cons b ys ih =>
    have ht : repeatCost k xs.length (b::ys).length =
        (4*k+6+(4*xs.length+10))+repeatCost (k+1) (xs++[b]).length ys.length := by
      simp only [List.length_cons,List.length_append,List.length_singleton]
      exact repeatCost_succ k xs.length ys.length
    rw [ht,run_add]
    simp only [List.length_cons,List.replicate_succ,List.cons_append,List.append_assoc]
    have hs := Source284MatchLoopComplete.both_step_rest continuation k
      (List.replicate ys.length false ++ tokens) xs (ys++rest) b certificate tail
    simp only [List.cons_append,List.append_assoc] at hs
    rw [hs,Source284MatchLoopComplete.replicate_mark]
    have hi := ih (k+1) (xs++[b])
    simp only [List.append_assoc] at hi
    rw [hi]
    simp [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def compareCost (n : Nat) : Nat := 4*n*n+24*n+20

theorem terminalCost (n : Nat) :
    compareCost n = repeatCost 1 0 n + (4*(1+n)+6+(4*n+10)) := by
  unfold compareCost repeatCost
  ring

/-- One leading marked pair is excluded from the original unary bound. -/
theorem equal_length (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨pairTape (true::List.replicate w.length false) certificate,
      2*flipped (w++[false]) tail,some 0⟩ (compareCost w.length) =
    ⟨pairTape (List.replicate (1+w.length) true) certificate,
      2*zeros w (flipped [false] tail),some 50⟩ := by
  have hp := repeat_pairs continuation 1 [] [] w [] certificate tail
  simp only [List.length_nil,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_nil,
    zeros] at hp
  rw [terminalCost,run_add,hp,Source284MatchLoop.exhausted_step]

theorem more_tokens (continuation : Nat → Bool → Row) (w : List Bool) (extra : Nat)
    (certificate tail : Nat) :
    run (table continuation) ⟨pairTape (true::List.replicate (w.length+1+extra) false) certificate,
      2*flipped (w++[false]) tail,some 0⟩ (compareCost w.length) =
    ⟨pairTape (List.replicate (1+w.length) true ++ true::List.replicate extra false) certificate,
      2*zeros w (flipped [false] tail),some 48⟩ := by
  have hp := repeat_pairs continuation 1 (false::List.replicate extra false) [] w [] certificate tail
  simp only [List.length_nil,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_nil,
    zeros] at hp
  have he : List.replicate w.length false ++ false::List.replicate extra false =
      List.replicate (w.length+1+extra) false := by
    rw [List.replicate_add,List.replicate_add]
    simp [List.append_assoc]
  rw [he] at hp
  rw [terminalCost,run_add,hp,Source284MatchLoop.token_step]

theorem more_payload (continuation : Nat → Bool → Row) (w rest : List Bool) (b : Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨pairTape (true::List.replicate w.length false) certificate,
      2*flipped ((w++b::rest)++[false]) tail,some 0⟩ (compareCost w.length) =
    ⟨pairTape (List.replicate (1+w.length) true) certificate,
      2*zeros (w++[b]) (flipped (rest++[false]) tail),some 49⟩ := by
  have hp := repeat_pairs continuation 1 [] [] w (b::rest) certificate tail
  simp only [List.length_nil,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_nil,
    zeros] at hp
  rw [terminalCost,run_add,hp]
  simpa using Source284MatchLoopComplete.payload_step_rest continuation (1+w.length) w rest b certificate tail

/-- The encoded source comparator classifies every prepared tape, with the
one marked prefix pair excluded from the supplied original cutoff. -/
theorem source_total_compare (states : Nat) (verifier : Nat → Bool → Row) (limit : Nat) (w : List Bool)
    (otherHalf tail : Nat) (hn : 0 < states) (hv : Closed states verifier) :
    ∃ left right mode,
      Source284Relative.run (Source284PreparedCutoff.description states verifier)
        (Source284Relative.initial (2*flipped (w++[false]) tail)
          (pairTape (true::List.replicate limit false) otherHalf))
        (compareCost (min limit w.length)) = ⟨left,right,active (48+mode)⟩ ∧
      (mode = 0 ↔ w.length < limit) ∧ (mode = 1 ↔ limit < w.length) ∧ (mode = 2 ↔ limit = w.length) := by
  let cont := Source284PreparedCutoff.router verifier
  have hc := Source284PreparedCutoff.router_closed states verifier hn hv
  have hsource : ∀ left right clock,
      Source284Relative.run (Source284PreparedCutoff.description states verifier)
        (Source284Relative.initial right left) clock =
      toSource (run (table cont) ⟨left,right,some 0⟩ clock) := by
    intro left right clock
    exact Source284MatchLoopSource.source_run (4+states) cont left right clock (by omega) hc
  rcases Nat.lt_trichotomy limit w.length with hlt | heq | hgt
  · have hdlen : 0 < (w.drop limit).length := by simp; omega
    cases hd : w.drop limit with
    | nil => simp [hd] at hdlen
    | cons b rest =>
      have hw : w = w.take limit ++ b::rest := by
        have h := List.take_append_drop limit w
        rw [hd] at h
        exact h.symm
      have hlen : (w.take limit).length = limit := by
        simp [List.length_take,Nat.min_eq_left (by omega : limit ≤ w.length)]
      let pref := w.take limit
      have hp := more_payload cont pref rest b otherHalf tail
      have hprefix : pref.length = limit := hlen
      rw [hprefix,← hw] at hp
      refine ⟨pairTape (List.replicate (1+limit) true) otherHalf,
        2*zeros (pref++[b]) (flipped (rest++[false]) tail),1,?_,?_,?_,?_⟩
      · rw [hsource]
        simpa [Nat.min_eq_left (by omega : limit ≤ w.length),hp,toSource,nextState,active]
      · simp; omega
      · simp [hlt]
      · simp; omega
  · subst limit
    refine ⟨pairTape (List.replicate (1+w.length) true) otherHalf,
      2*zeros w (flipped [false] tail),2,?_,?_,?_,?_⟩
    · rw [hsource,Nat.min_self,equal_length]
      rfl
    · simp
    · simp
    · simp
  · let extra := limit-(w.length+1)
    have he : w.length+1+extra = limit := by dsimp [extra]; omega
    have hp := more_tokens cont w extra otherHalf tail
    rw [he] at hp
    refine ⟨pairTape (List.replicate (1+w.length) true ++ true::List.replicate extra false) otherHalf,
      2*zeros w (flipped [false] tail),0,?_,?_,?_,?_⟩
    · rw [hsource]
      simpa [Nat.min_eq_right (by omega : w.length ≤ limit),hp,toSource,nextState,active]
    · simp [hgt]
    · simp; omega
    · simp; omega

/-- The offset comparator's reject mode is exactly the original bounded
decoder's reject condition, with a time bound independent of the suffix. -/
theorem source_decoder_classification (states : Nat) (verifier : Nat → Bool → Row)
    (limit : Nat) (w : List Bool) (suffix otherHalf : Nat)
    (hn : 0 < states) (hv : Closed states verifier) :
    ∃ left right mode t, t ≤ 4*limit*limit+24*limit+20 ∧
      Source284Relative.run (Source284PreparedCutoff.description states verifier)
        (Source284Relative.initial (2*flipped (w++[false]) suffix)
          (pairTape (true::List.replicate limit false) otherHalf)) t =
        ⟨left,right,active (48+mode)⟩ ∧
      (mode = 1 ↔ Source284WitnessWindow.decode limit (Source284Parser.encodeFrame w suffix) = none) ∧
      (mode = 0 ↔ w.length < limit) ∧ (mode = 2 ↔ limit = w.length) := by
  obtain ⟨left,right,mode,hr,h0,h1,h2⟩ := source_total_compare states verifier limit w otherHalf suffix hn hv
  refine ⟨left,right,mode,compareCost (min limit w.length),?_,hr,?_,h0,h2⟩
  · have hm : min limit w.length ≤ limit := Nat.min_le_left _ _
    have hp : min limit w.length * min limit w.length ≤ limit*limit := Nat.mul_le_mul hm hm
    unfold compareCost
    nlinarith
  · rw [Source284PreparedCutoff.decode_none_iff_length]
    exact h1

/-- Decoder-rejected witnesses never accept in the actual offset comparator,
including before its reject branch is reached. -/
theorem source_overlong_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (limit : Nat) (w : List Bool) (suffix otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (hover : Source284WitnessWindow.decode limit (Source284Parser.encodeFrame w suffix) = none) :
    ∀ clock, Source284Relative.accepts (Source284PreparedCutoff.description states verifier)
      (2*flipped (w++[false]) suffix) (pairTape (true::List.replicate limit false) otherHalf) clock = false := by
  obtain ⟨left,right,mode,t,_,hr,hm,_,_⟩ :=
    source_decoder_classification states verifier limit w suffix otherHalf hn hv
  have he : mode = 1 := hm.mpr hover
  subst mode
  apply Source284PositiveTaggedCutoff.never_of_after _ _ _ t
  intro extra
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,hr]
  simp only [beq_eq_false_iff_ne]
  exact Source284PreparedCutoff.source_reject_forever states verifier left right extra hn hv

/-- Within-cutoff witnesses reach the supplied verifier in one additional
paid turn, even when the original cutoff is zero. -/
theorem source_within_reaches_verifier (states : Nat) (verifier : Nat → Bool → Row)
    (limit : Nat) (w : List Bool) (suffix otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (hwithin : Source284WitnessWindow.decode limit (Source284Parser.encodeFrame w suffix) ≠ none) :
    ∃ left right t, t ≤ 4*limit*limit+24*limit+21 ∧
      Source284Relative.run (Source284PreparedCutoff.description states verifier)
        (Source284Relative.initial (2*flipped (w++[false]) suffix)
          (pairTape (true::List.replicate limit false) otherHalf)) t = ⟨right,left,active 52⟩ := by
  obtain ⟨left,right,mode,t,ht,hr,_,h0,h2⟩ :=
    source_decoder_classification states verifier limit w suffix otherHalf hn hv
  have hle : w.length ≤ limit := by
    by_contra h
    have hnone := (Source284PreparedCutoff.decode_none_iff_length limit w suffix).mpr (by omega)
    exact hwithin hnone
  have hm : mode = 0 ∨ mode = 2 := by
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact Or.inl (h0.mpr h)
    · exact Or.inr (h2.mpr h.symm)
  refine ⟨left,right,t+1,by omega,?_⟩
  rw [Source284Relative.run_add_clock,hr,
    Source284PreparedCutoff.source_good_turn states verifier mode left right hn hv hm]

/-- A raw numeric witness and one marked tag pair are handled by the same
finite conversion/comparison table. The full frame conversion is charged and
may depend on raw witness length; only the unary bound is pre-positioned. -/
theorem raw_overlong_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (limit input otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (hover : Source284WitnessWindow.decode limit input = none) :
    ∀ clock, Source284Relative.accepts (Source284CutoffPreparation.description states verifier) input
      (pairTape (true::List.replicate limit false) otherHalf) clock = false := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  rw [← hw] at hover ⊢
  have hover' : Source284WitnessWindow.decode limit
      (Source284Parser.encodeFrame w ((suffix/4)/4)) = none :=
    (Source284CutoffPreparation.decoder_suffix_invariant limit w suffix).mp hover
  apply Source284PositiveTaggedCutoff.never_of_after _ _ _
    (Source284PayloadSentinelPipeline.totalCost w.length)
  intro extra
  have hafter := Source284PayloadSentinelPipeline.source_after_pipeline
    (48+(4+states)) (Source284CutoffPreparation.comparator verifier) w
    (pairTape (true::List.replicate limit false) otherHalf) suffix extra (by omega)
    (Source284CutoffPreparation.comparator_closed states verifier hn hv)
  change Source284Relative.accepts (Source284CutoffPreparation.description states verifier)
      (Source284Parser.encodeFrame w suffix) (pairTape (true::List.replicate limit false) otherHalf)
      (Source284PayloadSentinelPipeline.totalCost w.length+extra) =
    Source284Relative.accepts (Source284PreparedCutoff.description states verifier)
      (2*flipped (w++[false]) ((suffix/4)/4))
      (pairTape (true::List.replicate limit false) otherHalf) extra at hafter
  rw [hafter]
  exact source_overlong_never_accepts states verifier limit w ((suffix/4)/4) otherHalf hn hv hover' extra

end Shared.Beeping.NPcoNP.Source284OffsetMatch
