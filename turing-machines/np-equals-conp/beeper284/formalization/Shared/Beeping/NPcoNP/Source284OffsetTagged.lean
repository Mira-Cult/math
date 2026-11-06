import Shared.Beeping.NPcoNP.Source284OffsetMatch

/-! One finite tagged-witness source table with an unmodified prepared unary
bound. The two tag cells become a unary pair; two paid turns mark that pair
so the comparator excludes it from the original bound, including bound zero.
Constructing the unary pairs and original input layout remains open. -/
set_option maxRecDepth 4096
namespace Shared.Beeping.NPcoNP.Source284OffsetTagged

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def markTable (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 1⟩
  else if q = 1 then ⟨true,true,some 2⟩
  else shiftRow 2 (continuation (q-2) b)

theorem mark_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (2+states) (markTable continuation) := by
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [markTable] at hnext; omega
  · by_cases h1 : q = 1
    · subst q; simp [markTable] at hnext; omega
    · have ht : (shiftRow 2 (continuation (q-2) b)).next = some q' := by
        simpa [markTable,h0,h1] using hnext
      cases he : (continuation (q-2) b).next with
      | none => simp [shiftRow,he] at ht
      | some r =>
        have h := hv (q-2) (by omega) b r he
        simp [shiftRow,he] at ht
        subst q'; omega

theorem mark_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    markTable continuation (2+q) b = shiftRow 2 (continuation q b) := by
  simp [markTable,show 2+q ≠ 1 by omega]

theorem mark_relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (markTable continuation) (shiftConfig 2 c) = shiftConfig 2 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,mark_row,shiftRow]
      split <;> rfl

theorem mark_relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (markTable continuation) (shiftConfig 2 c) fuel = shiftConfig 2 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,mark_relocated_step]

/-- The two turns mark the extra tag pair while restoring the head and the
complete raw witness half. -/
theorem mark_extra (continuation : Nat → Bool → Row) (limit otherHalf witness : Nat) :
    run (markTable continuation) ⟨4*pairTape (List.replicate limit false) otherHalf,witness,some 0⟩ 2 =
      ⟨pairTape (true::List.replicate limit false) otherHalf,witness,some 2⟩ := by
  have h0 : step (markTable continuation)
      ⟨4*pairTape (List.replicate limit false) otherHalf,witness,some 0⟩ =
      ⟨witness,4*pairTape (List.replicate limit false) otherHalf,some 1⟩ := by
    apply Source284WindowRewind.generic_turn
    intro b; simp [markTable]
  have h1 : step (markTable continuation)
      ⟨witness,4*pairTape (List.replicate limit false) otherHalf,some 1⟩ =
      ⟨4*pairTape (List.replicate limit false) otherHalf+1,witness,some 2⟩ := by
    simp [step,markTable,bit] <;> omega
  simp only [run,h0,h1]
  simp [pairTape,Source284PayloadLoop.scratch,bit] <;> omega

def rawStates (states : Nat) : Nat := Source284PositiveTaggedCutoff.rawStates states
def rawTable (verifier : Nat → Bool → Row) : Nat → Bool → Row := Source284PositiveTaggedCutoff.rawTable verifier
def goodStates (states : Nat) : Nat := 2+rawStates states
def goodTable (verifier : Nat → Bool → Row) : Nat → Bool → Row := markTable (rawTable verifier)
def table (states : Nat) (verifier : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284TaggedHandoff.table (goodStates states) (goodTable verifier) Source284TaggedHandoff.rejectTable
def description (states : Nat) (verifier : Nat → Bool → Row) : Nat :=
  encode (3+goodStates states+1) (table states verifier) 1

theorem good_closed (states : Nat) (verifier : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states verifier) :
    Closed (goodStates states) (goodTable verifier) :=
  mark_closed (rawStates states) (rawTable verifier) (by simp [rawStates,Source284PositiveTaggedCutoff.rawStates])
    (Source284PositiveTaggedCutoff.raw_closed states verifier hn hv)

theorem table_closed (states : Nat) (verifier : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states verifier) :
    Closed (3+goodStates states+1) (table states verifier) :=
  Source284TaggedHandoff.closed (goodStates states) 1 (goodTable verifier) Source284TaggedHandoff.rejectTable
    (by simp [goodStates]) (by omega) (good_closed states verifier hn hv) Source284TaggedHandoff.reject_closed

/-- A valid tag and its marking operation take four concrete source steps. -/
theorem source_tag_and_mark (states : Nat) (verifier : Nat → Bool → Row)
    (limit certificate otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (htag : certificate%4 = 0) :
    Source284Relative.run (description states verifier)
      (Source284Relative.initial certificate (pairTape (List.replicate limit false) otherHalf)) 4 =
      ⟨pairTape (true::List.replicate limit false) otherHalf,certificate/4,active 5⟩ := by
  let c : Config := ⟨pairTape (List.replicate limit false) otherHalf,certificate,some 0⟩
  have hc : Valid (3+goodStates states+1) c := by intro q hq; simp [c] at hq; subst q; omega
  have hr := run_toSource (3+goodStates states+1) (table states verifier) 1 c
    (table_closed states verifier hn hv) hc 4
  change Source284Relative.run (description states verifier)
    (Source284Relative.initial certificate (pairTape (List.replicate limit false) otherHalf)) 4 = _ at hr
  rw [hr]
  dsimp only [c,table]
  rw [show 4 = 2+2 by omega,Source284PayloadPop.run_add,Source284TaggedHandoff.dispatch]
  have h0 : certificate%2 = 0 := by omega
  have h1 : (certificate/2)%2 = 0 := by omega
  simp only [htag,h0,h1,↓reduceIte,Nat.mul_zero,Nat.add_zero]
  change toSource (run (Source284TaggedHandoff.table (goodStates states) (goodTable verifier)
    Source284TaggedHandoff.rejectTable)
      (shiftConfig 3 ⟨4*pairTape (List.replicate limit false) otherHalf,certificate/4,some 0⟩) 2) = _
  rw [Source284TaggedHandoff.good_run (goodStates states) (goodTable verifier)
    Source284TaggedHandoff.rejectTable _ (good_closed states verifier hn hv) (by
      intro q hq; simp at hq; subst q; simp [goodStates])]
  change toSource (shiftConfig 3 (run (markTable (rawTable verifier)) _ 2)) = _
  rw [mark_extra]
  rfl

/-- Following the paid tag check and mark, the same finite table has the
raw conversion/comparator acceptance behavior with the unchanged cutoff. -/
theorem accepts_after_valid_tag (states : Nat) (verifier : Nat → Bool → Row)
    (limit certificate otherHalf clock : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (htag : certificate%4 = 0) :
    Source284Relative.accepts (description states verifier) certificate
      (pairTape (List.replicate limit false) otherHalf) (4+clock) =
    Source284Relative.accepts (Source284CutoffPreparation.description states verifier) (certificate/4)
      (pairTape (true::List.replicate limit false) otherHalf) clock := by
  let c : Config := ⟨pairTape (true::List.replicate limit false) otherHalf,certificate/4,some 0⟩
  have hv0 : Valid (rawStates states) c := by
    intro q hq; simp [c] at hq; subst q; simp [rawStates,Source284PositiveTaggedCutoff.rawStates]
  have hv1 : Valid (goodStates states) (shiftConfig 2 c) := by
    intro q hq; simp [c,shiftConfig] at hq; subst q; simp [goodStates,rawStates,Source284PositiveTaggedCutoff.rawStates]
  have hv2 : Valid (3+goodStates states+1) (shiftConfig 3 (shiftConfig 2 c)) := by
    intro q hq; simp [c,shiftConfig] at hq; subst q; simp [goodStates,rawStates,Source284PositiveTaggedCutoff.rawStates] <;> omega
  have hr0 := run_toSource (rawStates states) (rawTable verifier) 1 c
    (Source284PositiveTaggedCutoff.raw_closed states verifier hn hv) hv0 clock
  have hr1 := run_toSource (3+goodStates states+1) (table states verifier) 1 (shiftConfig 3 (shiftConfig 2 c))
    (table_closed states verifier hn hv) hv2 clock
  change Source284Relative.run (encode (Source284PositiveTaggedCutoff.rawStates states)
    (Source284PositiveTaggedCutoff.rawTable verifier) 1) (toSource c) clock = _ at hr0
  rw [Source284PositiveTaggedCutoff.raw_description] at hr0
  change Source284Relative.run (Source284CutoffPreparation.description states verifier)
    (Source284Relative.initial (certificate/4) (pairTape (true::List.replicate limit false) otherHalf)) clock = _ at hr0
  change Source284Relative.run (description states verifier)
    ⟨pairTape (true::List.replicate limit false) otherHalf,certificate/4,active 5⟩ clock = _ at hr1
  change Source284Relative.run (description states verifier)
    ⟨pairTape (true::List.replicate limit false) otherHalf,certificate/4,active 5⟩ clock =
    toSource (run (Source284TaggedHandoff.table (goodStates states) (goodTable verifier)
      Source284TaggedHandoff.rejectTable) (shiftConfig 3 (shiftConfig 2 c)) clock) at hr1
  rw [Source284TaggedHandoff.good_run (goodStates states) (goodTable verifier)
    Source284TaggedHandoff.rejectTable _ (good_closed states verifier hn hv) hv1] at hr1
  change Source284Relative.run (description states verifier)
    ⟨pairTape (true::List.replicate limit false) otherHalf,certificate/4,active 5⟩ clock =
    toSource (shiftConfig 3 (run (markTable (rawTable verifier)) (shiftConfig 2 c) clock)) at hr1
  rw [mark_relocated_run] at hr1
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_tag_and_mark states verifier limit certificate otherHalf hn hv htag,
    hr1,hr0]
  cases hs : (run (rawTable verifier) c clock).state <;>
    simp [toSource,shiftConfig,nextState,hs,active]

/-- Under a valid tag, every overlong witness is rejected at every clock,
for every original bound, without a special zero branch. -/
theorem valid_overlong_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (limit certificate otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (htag : certificate%4 = 0) (hbad : Source284TaggedWitnessCodec.decode limit certificate = none) :
    ∀ clock, Source284Relative.accepts (description states verifier) certificate
      (pairTape (List.replicate limit false) otherHalf) clock = false := by
  have hraw : Source284WitnessWindow.decode limit (certificate/4) = none := by
    simpa [Source284TaggedWitnessCodec.decode,htag] using hbad
  apply Source284PositiveTaggedCutoff.never_of_after _ _ _ 4
  intro extra
  rw [accepts_after_valid_tag states verifier limit certificate otherHalf extra hn hv htag]
  exact Source284OffsetMatch.raw_overlong_never_accepts states verifier limit (certificate/4) otherHalf hn hv hraw extra

theorem source_bad_dispatch (states : Nat) (verifier : Nat → Bool → Row)
    (limit certificate otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (htag : certificate%4 ≠ 0) :
    Source284Relative.run (description states verifier)
      (Source284Relative.initial certificate (pairTape (List.replicate limit false) otherHalf)) 2 =
      ⟨4*pairTape (List.replicate limit false) otherHalf+2*(certificate%2)+(certificate/2)%2,
        certificate/4,active (3+goodStates states)⟩ := by
  let c : Config := ⟨pairTape (List.replicate limit false) otherHalf,certificate,some 0⟩
  have hc : Valid (3+goodStates states+1) c := by intro q hq; simp [c] at hq; subst q; omega
  have hr := run_toSource (3+goodStates states+1) (table states verifier) 1 c
    (table_closed states verifier hn hv) hc 2
  change Source284Relative.run (description states verifier)
    (Source284Relative.initial certificate (pairTape (List.replicate limit false) otherHalf)) _ = _ at hr
  rw [hr]
  dsimp only [c,table]
  rw [Source284TaggedHandoff.dispatch]
  simp [htag,toSource,nextState,active]

theorem reject_entry_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (left right clock : Nat) (hn : 0 < states) (hv : Closed states verifier) :
    (Source284Relative.run (description states verifier) ⟨left,right,active (3+goodStates states)⟩ clock).state ≠ 0 := by
  let c : Config := ⟨left,right,some 0⟩
  have hc : Valid (3+goodStates states+1) (shiftConfig (3+goodStates states) c) := by
    intro q hq; simp [c,shiftConfig] at hq; subst q; omega
  have hr := run_toSource (3+goodStates states+1) (table states verifier) 1
    (shiftConfig (3+goodStates states) c) (table_closed states verifier hn hv) hc clock
  change Source284Relative.run (description states verifier) ⟨left,right,active (3+goodStates states)⟩ clock =
    toSource (run (Source284TaggedHandoff.table (goodStates states) (goodTable verifier)
      Source284TaggedHandoff.rejectTable) (shiftConfig (3+goodStates states) c) clock) at hr
  rw [Source284TaggedHandoff.bad_run] at hr
  rw [hr]
  have hs := Source284TaggedHandoff.reject_run_state left right clock
  change (run Source284TaggedHandoff.rejectTable c clock).state = some 0 at hs
  cases hrun : run Source284TaggedHandoff.rejectTable c clock with
  | mk l r q =>
    have hq : q = some 0 := by simpa [hrun] using hs
    subst q
    simp [shiftConfig,toSource,nextState,active,goodStates,rawStates,Source284PositiveTaggedCutoff.rawStates]

theorem invalid_tag_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (limit certificate otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (htag : certificate%4 ≠ 0) :
    ∀ clock, Source284Relative.accepts (description states verifier) certificate
      (pairTape (List.replicate limit false) otherHalf) clock = false := by
  apply Source284PositiveTaggedCutoff.never_of_after _ _ _ 2
  intro extra
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_bad_dispatch states verifier limit certificate otherHalf hn hv htag]
  simp only [beq_eq_false_iff_ne]
  exact reject_entry_never_accepts states verifier _ _ extra hn hv

/-- One fixed finite source table enforces the original tagged witness
cutoff for every prepared unary bound, including zero, at every clock. -/
theorem decoded_none_never_accepts (states : Nat) (verifier : Nat → Bool → Row)
    (limit certificate otherHalf : Nat) (hn : 0 < states) (hv : Closed states verifier)
    (hbad : Source284TaggedWitnessCodec.decode limit certificate = none) :
    ∀ clock, Source284Relative.accepts (description states verifier) certificate
      (pairTape (List.replicate limit false) otherHalf) clock = false := by
  by_cases htag : certificate%4 = 0
  · exact valid_overlong_never_accepts states verifier limit certificate otherHalf hn hv htag hbad
  · exact invalid_tag_never_accepts states verifier limit certificate otherHalf hn hv htag

namespace Fixtures
open Source284PreparedCutoff.Fixtures (acceptImmediately accept_closed)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

/-- For the concrete always-accepting verifier, every accepted decoder
witness reaches acceptance. This checks that the guard is not vacuous. -/
theorem decoded_some_bounded_accepts (limit certificate otherHalf : Nat)
    (hgood : Source284TaggedWitnessCodec.decode limit certificate ≠ none) :
    ∃ clock, clock ≤ 4+Source284PayloadSentinelPipeline.totalCost
        (Source284Parser.length (certificate/4))+4*limit*limit+24*limit+22 ∧
      Source284Relative.accepts (description 1 acceptImmediately) certificate
        (pairTape (List.replicate limit false) otherHalf) clock = true := by
  have htag : certificate%4 = 0 := by
    by_contra h
    apply hgood
    simp [Source284TaggedWitnessCodec.decode,h]
  have hraw : Source284WitnessWindow.decode limit (certificate/4) ≠ none := by
    simpa [Source284TaggedWitnessCodec.decode,htag] using hgood
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective (certificate/4)
  have hraw' : Source284WitnessWindow.decode limit (Source284Parser.encodeFrame w suffix) ≠ none := by
    simpa [hw] using hraw
  have hwithin : Source284WitnessWindow.decode limit (Source284Parser.encodeFrame w ((suffix/4)/4)) ≠ none := by
    intro hn
    exact hraw' ((Source284CutoffPreparation.decoder_suffix_invariant limit w suffix).mpr hn)
  obtain ⟨left,right,t,htime,hr⟩ := Source284OffsetMatch.source_within_reaches_verifier
    1 acceptImmediately limit w ((suffix/4)/4) otherHalf (by omega) accept_closed hwithin
  have hv := Source284PreparedCutoff.source_after_verifier 1 acceptImmediately 0 right left 1
    (by omega) (by omega) accept_closed
  change Source284Relative.run (Source284PreparedCutoff.description 1 acceptImmediately)
    ⟨right,left,active 52⟩ 1 = _ at hv
  have hc : Source284Relative.accepts (Source284PreparedCutoff.description 1 acceptImmediately)
      (2*flipped (w++[false]) ((suffix/4)/4))
      (pairTape (true::List.replicate limit false) otherHalf) (t+1) = true := by
    unfold Source284Relative.accepts
    rw [Source284Relative.run_add_clock,hr,hv]
    simp [acceptImmediately,run,step,shiftConfig,toSource,nextState]
  have hprep := Source284PayloadSentinelPipeline.source_after_pipeline
    (48+(4+1)) (Source284CutoffPreparation.comparator acceptImmediately) w
    (pairTape (true::List.replicate limit false) otherHalf) suffix (t+1) (by omega)
    (Source284CutoffPreparation.comparator_closed 1 acceptImmediately (by omega) accept_closed)
  change Source284Relative.accepts (Source284CutoffPreparation.description 1 acceptImmediately)
      (Source284Parser.encodeFrame w suffix) (pairTape (true::List.replicate limit false) otherHalf)
      (Source284PayloadSentinelPipeline.totalCost w.length+(t+1)) = _ at hprep
  have hrawaccept := hprep.trans hc
  rw [hw] at hrawaccept
  let clock := Source284PayloadSentinelPipeline.totalCost w.length+(t+1)
  have ht := accepts_after_valid_tag 1 acceptImmediately limit certificate otherHalf clock
    (by omega) accept_closed htag
  have hlen : Source284Parser.length (certificate/4) = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨4+clock,?_,ht.trans hrawaccept⟩
  dsimp [clock]
  rw [hlen]
  omega

theorem decoded_some_eventually_accepts (limit certificate otherHalf : Nat)
    (hgood : Source284TaggedWitnessCodec.decode limit certificate ≠ none) :
    ∃ clock, Source284Relative.accepts (description 1 acceptImmediately) certificate
      (pairTape (List.replicate limit false) otherHalf) clock = true := by
  obtain ⟨clock,_,h⟩ := decoded_some_bounded_accepts limit certificate otherHalf hgood
  exact ⟨clock,h⟩

/-- An accepting verifier accepts exactly the tagged decoder's valid codes,
for every cutoff and every high-suffix alias. -/
theorem accepting_verifier_iff (limit certificate otherHalf : Nat) :
    (∃ clock, Source284Relative.accepts (description 1 acceptImmediately) certificate
      (pairTape (List.replicate limit false) otherHalf) clock = true) ↔
        Source284TaggedWitnessCodec.decode limit certificate ≠ none := by
  constructor
  · rintro ⟨clock,h⟩ hnone
    have hfalse := decoded_none_never_accepts 1 acceptImmediately limit certificate otherHalf
      (by omega) accept_closed hnone clock
    rw [hfalse] at h
    contradiction
  · exact decoded_some_eventually_accepts limit certificate otherHalf

example : Source284TaggedWitnessCodec.decode 0 4 = none := by decide +kernel
example : Source284TaggedWitnessCodec.decode 0 0 ≠ none := by decide +kernel
example : Source284TaggedWitnessCodec.decode 1 4 ≠ none := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284OffsetTagged
